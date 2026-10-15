# 2-gram 索引の形ごとの大きさ・作成時間・検索時間・最大メモリを測る。GitHub Actions（.github/workflows/gram.yml）から段階ごとに呼ぶ。
#
# 測るのは「本文インデックスのファイル（またはその一部のブロック）ごとの 2-gram の集合」から作る、gram -> ファイルの番号 の表の形。
# 使うのは .NET の標準の部品だけ（FileStream・BinaryWriter・Buffer.BlockCopy・Array.Sort・Array.BinarySearch・HashSet・MemoryMappedFile）。
# Add-Type・P/Invoke・子プロセスは使わない（段階ごとに別のプロセスで動かすのは、呼ぶ側のワークフロー）。
#
# 段階（-Stage）:
#   前の段階の結果が要る段階（無いと止まる）: build・segbuild・merge・segsearch は prep の grams\meta.json、search は prep の queries.json と build の表・unitfile.bin・結果の JSON、
#   merge は segbuild の seg_base、segsearch は segbuild の seg_base・seg_N・seg_rewrite、merge の merged_N、build の shape_list_files を読む。
#   defenderon・prep・summary は単独で動く。share・defender は、前の段階のファイルが無ければ、その項目を飛ばして記録する。
#   defenderon リアルタイム保護を有効にする方向に設定を変え、前後の状態を記録する（無効にする方向の変更はしない）
#   prep      データを作り（または読み）、ファイルごと・ブロックごとの 2-gram の集合を Work\grams に書く。検索語の表も作る
#   build     -Shape（list / bitset / mixed）と -Unit（files / blocks）の表を作る。-Label で結果の名前に印を付ける（-Parts を変えた作り直しなど）
#   search    作った表で語を検索する。FileStream で全部読む方法・FileStream の位置指定で二分探索する方法・MemoryMappedFile で読む方法を比べる
#   segbuild  区画の追加の時間を測る（土台 1 つ + ファイル 1 つの区画 7 つ + 書き直しの区画）
#   merge     区画をまとめ直す時間と最大メモリを測る（-SegmentCount 2 または 8）
#   segsearch 区画が 8 つのときと、まとめ直した後の検索を比べる。書き直したファイルの古い行を無効にする確かめも行う
#   share     MemoryMappedFile で開いている間の File.Delete / File.Move / File.Replace の成否と、世代の入れ替えの流れを測る
#   defender  大きいファイルを初めて開く時間と 2 回目の時間を測る
#   summary   Out の結果を Markdown にまとめる
#
# -Dataset perfdata は、tebunko-perfdata の new_index.ps1 が作ったフォルダ（-Index）の 部署N\年度M を本文インデックス 1 ファイルとみなす。
# -Dataset zipf は、語の出方に偏りを付けた乱数の文章（出現の多い語と、ファイルごとにほぼ 1 回しか出ない語）を作る。
param (
    [Parameter(Mandatory = $true)][ValidateSet("defenderon", "prep", "build", "search", "segbuild", "merge", "segsearch", "share", "defender", "summary")][string]$Stage,
    [ValidateSet("perfdata", "zipf")][string]$Dataset = "zipf",
    [Parameter(Mandatory = $true)][string]$Work,
    [Parameter(Mandatory = $true)][string]$Out,
    [string]$Index = "",
    [double]$Scale = 1.0,
    [ValidateSet("list", "bitset", "mixed")][string]$Shape = "list",
    [ValidateSet("files", "blocks")][string]$Unit = "files",
    [int]$Parts = 8,
    [int]$Workers = 4,
    [int]$BlockChars = 65536,
    [int]$SegmentCount = 8,
    [int]$Repeat = 5,
    [string]$Label = ""
)

$ErrorActionPreference = "Stop"
[void][System.IO.Directory]::CreateDirectory($Work)
[void][System.IO.Directory]::CreateDirectory($Out)
$Work = (Resolve-Path -LiteralPath $Work).ProviderPath.TrimEnd("\")
$Out = (Resolve-Path -LiteralPath $Out).ProviderPath.TrimEnd("\")
$gramFolder = Join-Path $Work "grams"
$shapeFolder = Join-Path $Work "shape_${Shape}_${Unit}$Label"
$culture = [System.Globalization.CultureInfo]::InvariantCulture
$utf8NoBom = New-Object System.Text.UTF8Encoding($false)
$bitMasks = [byte[]](1, 2, 4, 8, 16, 32, 64, 128)

# ---------------------------------------------------------------- 共通の部品

function getPeakMegabytes {
    return [int][Math]::Round([System.Diagnostics.Process]::GetCurrentProcess().PeakWorkingSet64 / 1MB)
}

function writeResult {
    param ([string]$name, $data)
    $json = $data | ConvertTo-Json -Depth 8
    [System.IO.File]::WriteAllText((Join-Path $Out "$name.json"), $json, $utf8NoBom)
    Write-Host ("結果を書きました: {0}.json（{1} バイト、最大メモリ {2} MB）" -f $name, $json.Length, (getPeakMegabytes))
}

function readResult {
    param ([string]$name)
    $path = Join-Path $Out "$name.json"
    if (![System.IO.File]::Exists($path)) { return $null }
    return ConvertFrom-Json ([System.IO.File]::ReadAllText($path, $utf8NoBom))
}

function getStats {
    param ($values)
    $sorted = [double[]]@($values | Sort-Object)
    if ($sorted.Length -eq 0) { return [ordered]@{ Count = 0; Min = 0; Median = 0; P90 = 0; Max = 0 } }
    $median = $sorted[[int][Math]::Floor(($sorted.Length - 1) * 0.5)]
    $p90 = $sorted[[int][Math]::Floor(($sorted.Length - 1) * 0.9)]
    return [ordered]@{ Count = $sorted.Length; Min = $sorted[0]; Median = $median; P90 = $p90; Max = $sorted[$sorted.Length - 1] }
}

function getLowerBound {
    # 昇順で重複の無い配列の中で、target 以上の最初の位置
    param ($values, [uint32]$target)
    $found = [Array]::BinarySearch($values, $target)
    if ($found -lt 0) { $found = -bnot $found }
    return $found
}

function fillRepeated {
    # array[start] に入れた 1 つの値を、start から count 個に広げる（Buffer.BlockCopy を倍々に使う）
    param ($array, [int]$start, [int]$count, [int]$elementBytes)
    $filled = 1
    while ($filled -lt $count) {
        $copyCount = [Math]::Min($filled, $count - $filled)
        [System.Buffer]::BlockCopy($array, $start * $elementBytes, $array, ($start + $filled) * $elementBytes, $copyCount * $elementBytes)
        $filled += $copyCount
    }
}

function writeArraySlice {
    param ($stream, $array, [int]$elementBytes, [long]$startIndex, [long]$count)
    $chunkElements = [int](4MB / $elementBytes)
    $buffer = New-Object byte[] ($chunkElements * $elementBytes)
    $position = $startIndex
    $end = $startIndex + $count
    while ($position -lt $end) {
        $take = [int][Math]::Min($chunkElements, $end - $position)
        [System.Buffer]::BlockCopy($array, [int]($position * $elementBytes), $buffer, 0, $take * $elementBytes)
        $stream.Write($buffer, 0, $take * $elementBytes)
        $position += $take
    }
}

function openShared {
    param ([string]$path)
    return [System.IO.FileStream]::new($path, [System.IO.FileMode]::Open, [System.IO.FileAccess]::Read, ([System.IO.FileShare]::ReadWrite -bor [System.IO.FileShare]::Delete))
}

function readBytes {
    param ($stream, [long]$position, [int]$count)
    $buffer = New-Object byte[] $count
    if ($count -eq 0) { return , $buffer }
    [void]$stream.Seek($position, [System.IO.SeekOrigin]::Begin)
    $done = 0
    while ($done -lt $count) {
        $read = $stream.Read($buffer, $done, $count - $done)
        if ($read -le 0) { throw "ファイルが途中で終わっています" }
        $done += $read
    }
    return , $buffer
}

function readUInt32Array {
    param ($stream, [long]$position, [int]$count)
    $bytes = readBytes $stream $position ($count * 4)
    $values = New-Object 'uint32[]' $count
    if ($count -gt 0) { [System.Buffer]::BlockCopy($bytes, 0, $values, 0, $count * 4) }
    return , $values
}

function readUInt16Array {
    param ($stream, [long]$position, [int]$count)
    $bytes = readBytes $stream $position ($count * 2)
    $values = New-Object 'uint16[]' $count
    if ($count -gt 0) { [System.Buffer]::BlockCopy($bytes, 0, $values, 0, $count * 2) }
    return , $values
}

function readWholeUInt32 {
    param ([string]$path)
    $bytes = [System.IO.File]::ReadAllBytes($path)
    $values = New-Object 'uint32[]' ($bytes.Length / 4)
    if ($values.Length -gt 0) { [System.Buffer]::BlockCopy($bytes, 0, $values, 0, $bytes.Length) }
    return , $values
}

function readWholeUInt16 {
    param ([string]$path)
    $bytes = [System.IO.File]::ReadAllBytes($path)
    $values = New-Object 'uint16[]' ($bytes.Length / 2)
    if ($values.Length -gt 0) { [System.Buffer]::BlockCopy($bytes, 0, $values, 0, $bytes.Length) }
    return , $values
}

function getSearchGramValues {
    # 検索語から 2-gram の値（uint32。addTextGrams と同じ規則）を返す。重複なし・最大 16 個（多いときは均等に間引く）
    param ([string]$word)
    $grams = New-Object 'System.Collections.Generic.List[uint32]'
    $seen = New-Object 'System.Collections.Generic.HashSet[uint32]'
    foreach ($part in ([string]$word).ToLowerInvariant() -split "[\s ]+") {
        for ($position = 0; $position -lt $part.Length - 1; $position++) {
            $value = [uint32]([long][int]$part[$position] + 65536L * [long][int]$part[$position + 1])
            if ($seen.Add($value)) { $grams.Add($value) }
        }
    }
    if ($grams.Count -le 16) { return , $grams.ToArray() }
    $picked = New-Object 'System.Collections.Generic.List[uint32]'
    for ($index = 0; $index -lt 16; $index++) {
        $picked.Add($grams[[int][Math]::Round($index * ($grams.Count - 1) / 15)])
    }
    return , $picked.ToArray()
}

function convertGramToText {
    param ([uint32]$value)
    return ([string][char]($value -band 0xFFFF)) + ([string][char]($value -shr 16))
}

# ---------------------------------------------------------------- prep（スレッドごとの処理）

$workerScript = {
    param ($task, $dataset, $unitIndex, $source, $poolText, $blockChars, $gramFolder, $seed, $words)
    $ErrorActionPreference = "Stop"
    $timer = [System.Diagnostics.Stopwatch]::StartNew()

    function addTextGrams {
        param ($gramSet, [string]$text)
        $chars = $text.ToLowerInvariant().ToCharArray()
        $even = $chars.Length -shr 1
        $odd = ($chars.Length - 1) -shr 1
        if ($even -gt 0) {
            $values = New-Object 'uint32[]' $even
            [System.Buffer]::BlockCopy($chars, 0, $values, 0, $even * 4)
            $gramSet.UnionWith($values)
        }
        if ($odd -gt 0) {
            $values = New-Object 'uint32[]' $odd
            [System.Buffer]::BlockCopy($chars, 2, $values, 0, $odd * 4)
            $gramSet.UnionWith($values)
        }
    }

    if ($dataset -eq "perfdata") {
        $builder = New-Object System.Text.StringBuilder
        foreach ($path in [System.IO.Directory]::GetFiles($source, "*.tsv", [System.IO.SearchOption]::AllDirectories)) {
            [void]$builder.Append([System.IO.File]::ReadAllText($path)).Append("`n")
        }
        $text = $builder.ToString()
    } else {
        $random = [System.Random]::new($seed * 1000 + $unitIndex)
        $length = 600000 + $random.Next(100000)
        $offset = $random.Next($poolText.Length - $length)
        $builder = New-Object System.Text.StringBuilder ($length + 60000)
        [void]$builder.Append($poolText, $offset, $length)
        # ファイルごとに 1 回しか出ない語（人名・番号・型番など）に当たる、乱数の漢字の並び
        for ($count = 0; $count -lt 30000; $count++) { [void]$builder.Append([char](0x4E00 + $random.Next(0x5200))) }
        for ($count = 0; $count -lt 20000; $count++) { [void]$builder.Append([char](48 + $random.Next(10))) }
        $text = $builder.ToString()
    }

    if ($task -eq "truth") {
        $found = New-Object 'System.Collections.Generic.List[int]'
        for ($wordIndex = 0; $wordIndex -lt $words.Count; $wordIndex++) {
            if ($text.IndexOf([string]$words[$wordIndex], [System.StringComparison]::OrdinalIgnoreCase) -ge 0) { $found.Add($wordIndex) }
        }
        return [pscustomobject]@{ UnitIndex = $unitIndex; Found = $found.ToArray() }
    }

    # ブロック（blockChars 文字。隣のブロックとの境目の 2 文字を落とさないよう、1 文字重ねる）ごとの集合と、その和（ファイルの集合）
    # 重ねは 1 文字なので、境目をまたぐ 3 文字以上の語は、1 つのブロックがその語の gram を全部は持たず、ブロック単位では漏れうる（ファイル単位では漏れない）。
    # 測った「漏れ」の数は、その語が見本に無かっただけで、漏れないことの証明ではない。
    $fileSet = New-Object 'System.Collections.Generic.HashSet[uint32]'
    $blockStream = New-Object System.IO.MemoryStream
    $writer = New-Object System.IO.BinaryWriter $blockStream
    $blockSizes = New-Object 'System.Collections.Generic.List[int]'
    for ($start = 0; $start -lt $text.Length - 1; $start += $blockChars) {
        $length = [Math]::Min($blockChars + 1, $text.Length - $start)
        $blockSet = New-Object 'System.Collections.Generic.HashSet[uint32]'
        addTextGrams $blockSet $text.Substring($start, $length)
        $values = New-Object 'uint32[]' $blockSet.Count
        $blockSet.CopyTo($values)
        [Array]::Sort($values)
        $bytes = New-Object byte[] ($values.Length * 4)
        [System.Buffer]::BlockCopy($values, 0, $bytes, 0, $bytes.Length)
        $writer.Write([int]$values.Length)
        $writer.Write($bytes)
        $blockSizes.Add($values.Length)
        $fileSet.UnionWith($values)
    }
    $writer.Flush()
    [System.IO.File]::WriteAllBytes((Join-Path $gramFolder "blocks_$unitIndex.bin"), $blockStream.ToArray())
    $fileValues = New-Object 'uint32[]' $fileSet.Count
    $fileSet.CopyTo($fileValues)
    [Array]::Sort($fileValues)
    $fileBytes = New-Object byte[] ($fileValues.Length * 4)
    [System.Buffer]::BlockCopy($fileValues, 0, $fileBytes, 0, $fileBytes.Length)
    [System.IO.File]::WriteAllBytes((Join-Path $gramFolder "files_$unitIndex.u32"), $fileBytes)

    # 検索語の見本（本文の中の 3 文字）
    $samples = New-Object 'System.Collections.Generic.List[string]'
    $sampleRandom = [System.Random]::new($seed * 7919 + $unitIndex)
    for ($attempt = 0; $attempt -lt 60 -and $samples.Count -lt 3 -and $text.Length -gt 10; $attempt++) {
        $candidate = $text.Substring($sampleRandom.Next($text.Length - 3), 3)
        if ($candidate -match '^[^\s "\\]{3}$') { $samples.Add($candidate) }
    }
    # まれな語の見本（zipf のみ）: ファイルごとに 1 回しか出ない乱数の漢字の並び（末尾の 50000 文字のうち前半の 30000 文字）から、3 文字と 4 文字を取る
    $rareSamples = New-Object 'System.Collections.Generic.List[string]'
    if ($dataset -eq "zipf" -and $unitIndex -lt 6) {
        $rareStart = $text.Length - 50000
        $rareRandom = [System.Random]::new($seed * 104729 + $unitIndex)
        $rareSamples.Add($text.Substring($rareStart + $rareRandom.Next(29000), 3))
        $rareSamples.Add($text.Substring($rareStart + $rareRandom.Next(29000), 4))
    }
    return [pscustomobject]@{
        UnitIndex   = $unitIndex
        Chars       = $text.Length
        Distinct    = $fileValues.Length
        Blocks      = $blockSizes.ToArray()
        Samples     = $samples.ToArray()
        RareSamples = $rareSamples.ToArray()
        Seconds     = $timer.Elapsed.TotalSeconds
    }
}

function invokeWorkers {
    param ($argumentSets)
    $pool = [runspacefactory]::CreateRunspacePool(1, $Workers)
    $pool.Open()
    $jobs = New-Object System.Collections.ArrayList
    foreach ($arguments in $argumentSets) {
        $shell = [powershell]::Create()
        $shell.RunspacePool = $pool
        [void]$shell.AddScript($workerScript.ToString())
        foreach ($argument in $arguments) { [void]$shell.AddArgument($argument) }
        [void]$jobs.Add([pscustomobject]@{ Shell = $shell; Handle = $shell.BeginInvoke() })
    }
    $results = New-Object System.Collections.ArrayList
    foreach ($job in $jobs) {
        $output = $job.Shell.EndInvoke($job.Handle)
        if ($job.Shell.HadErrors) { throw $job.Shell.Streams.Error[0].ToString() }
        [void]$results.Add($output[0])
        $job.Shell.Dispose()
    }
    $pool.Close()
    return , $results.ToArray()
}

function newZipfPool {
    # 語の出方に偏りがある文章。文字は漢字 3000・ひらがな・カタカナ。語は 2〜5 文字の 10 万語。語の選び方は r^3 で先頭に偏らせる
    $random = [System.Random]::new(11)
    $alphabet = New-Object 'System.Collections.Generic.List[char]'
    for ($code = 0x4E00; $code -lt 0x4E00 + 3000; $code++) { $alphabet.Add([char]$code) }
    for ($code = 0x3041; $code -le 0x3093; $code++) { $alphabet.Add([char]$code) }
    for ($code = 0x30A1; $code -le 0x30F3; $code++) { $alphabet.Add([char]$code) }
    $vocabulary = New-Object 'string[]' 100000
    for ($wordIndex = 0; $wordIndex -lt $vocabulary.Length; $wordIndex++) {
        $length = 2 + $random.Next(4)
        $chars = New-Object char[] $length
        for ($position = 0; $position -lt $length; $position++) {
            $draw = $random.NextDouble()
            $chars[$position] = $alphabet[[int][Math]::Floor($alphabet.Count * $draw * $draw * $draw)]
        }
        $vocabulary[$wordIndex] = New-Object string (, $chars)
    }
    $builder = New-Object System.Text.StringBuilder (9000000)
    $count = 0
    while ($builder.Length -lt 8000000) {
        $draw = $random.NextDouble()
        [void]$builder.Append($vocabulary[[int][Math]::Floor($vocabulary.Length * $draw * $draw * $draw)])
        $count++
        if ($count % 8 -eq 0) { [void]$builder.Append("`n") } elseif ($count % 3 -eq 0) { [void]$builder.Append("`t") }
    }
    return $builder.ToString()
}

function invokePrep {
    $totalTimer = [System.Diagnostics.Stopwatch]::StartNew()
    [void][System.IO.Directory]::CreateDirectory($gramFolder)
    $sources = New-Object System.Collections.ArrayList
    $poolText = ""
    if ($Dataset -eq "perfdata") {
        if (!$Index) { throw "-Dataset perfdata には -Index が要ります" }
        foreach ($department in ([System.IO.Directory]::GetDirectories($Index) | Sort-Object)) {
            foreach ($year in ([System.IO.Directory]::GetDirectories($department) | Sort-Object)) { [void]$sources.Add($year) }
        }
    } else {
        $poolText = newZipfPool
        $unitCount = [Math]::Max(4, [int][Math]::Round(502 * $Scale))
        for ($unitIndex = 0; $unitIndex -lt $unitCount; $unitIndex++) { [void]$sources.Add("zipf") }
    }
    Write-Host ("本文インデックス 1 ファイルに当たる単位: {0} 個" -f $sources.Count)

    $argumentSets = New-Object System.Collections.ArrayList
    for ($unitIndex = 0; $unitIndex -lt $sources.Count; $unitIndex++) {
        [void]$argumentSets.Add(@("grams", $Dataset, $unitIndex, $sources[$unitIndex], $poolText, $BlockChars, $gramFolder, 1, @()))
    }
    $gramTimer = [System.Diagnostics.Stopwatch]::StartNew()
    $results = invokeWorkers $argumentSets
    $gramSeconds = $gramTimer.Elapsed.TotalSeconds

    $chars = [long]0
    $blockCounts = New-Object 'System.Collections.Generic.List[int]'
    $blockSizes = New-Object 'System.Collections.Generic.List[double]'
    $samples = New-Object 'System.Collections.Generic.List[string]'
    $rareCandidates = New-Object 'System.Collections.Generic.List[string]'
    foreach ($result in $results) {
        $chars += $result.Chars
        $blockCounts.Add(@($result.Blocks).Count)
        foreach ($size in @($result.Blocks)) { $blockSizes.Add($size) }
        foreach ($sample in @($result.Samples)) { $samples.Add($sample) }
        foreach ($sample in @($result.RareSamples)) { $rareCandidates.Add($sample) }
    }

    # 検索語: 該当無し・まれ・見本の 3 文字・見本の先頭 2 文字
    # まれな語は、perfdata では見積書。zipf では、ファイルごとに 1 回しか出ない乱数の漢字の並びから取った語のうち、含むファイルが 1〜3 個のもの（下で真の数を数えてから絞る）
    $random = [System.Random]::new(5)
    $words = New-Object System.Collections.ArrayList
    [void]$words.Add([pscustomobject]@{ Word = "該当無し"; Kind = "zero" })
    if ($Dataset -eq "perfdata") {
        [void]$words.Add([pscustomobject]@{ Word = "見積書"; Kind = "rare" })
    } else {
        foreach ($rare in $rareCandidates) { [void]$words.Add([pscustomobject]@{ Word = $rare; Kind = "rare" }) }
    }
    $shuffled = @($samples | Sort-Object { $random.Next() } | Select-Object -Unique)
    foreach ($sample in ($shuffled | Select-Object -First 40)) { [void]$words.Add([pscustomobject]@{ Word = $sample; Kind = "sample3" }) }
    foreach ($sample in ($shuffled | Select-Object -Skip 40 -First 10)) { [void]$words.Add([pscustomobject]@{ Word = $sample.Substring(0, 2); Kind = "sample2" }) }

    $truthTimer = [System.Diagnostics.Stopwatch]::StartNew()
    $wordTexts = [string[]]@($words | ForEach-Object { $_.Word })
    $truthSets = New-Object System.Collections.ArrayList
    for ($unitIndex = 0; $unitIndex -lt $sources.Count; $unitIndex++) {
        [void]$truthSets.Add(@("truth", $Dataset, $unitIndex, $sources[$unitIndex], $poolText, $BlockChars, $gramFolder, 1, $wordTexts))
    }
    $truthResults = invokeWorkers $truthSets
    $trueFiles = @{}
    foreach ($result in $truthResults) {
        foreach ($wordIndex in @($result.Found)) {
            if (!$trueFiles.ContainsKey([int]$wordIndex)) { $trueFiles[[int]$wordIndex] = New-Object 'System.Collections.Generic.List[int]' }
            $trueFiles[[int]$wordIndex].Add($result.UnitIndex)
        }
    }
    $queries = New-Object System.Collections.ArrayList
    for ($wordIndex = 0; $wordIndex -lt $words.Count; $wordIndex++) {
        $files = if ($trueFiles.ContainsKey($wordIndex)) { $trueFiles[$wordIndex].ToArray() } else { @() }
        if ($Dataset -eq "zipf" -and $words[$wordIndex].Kind -eq "rare" -and (@($files).Count -lt 1 -or @($files).Count -gt 3)) { continue }
        [void]$queries.Add([pscustomobject]@{ Word = $words[$wordIndex].Word; Kind = $words[$wordIndex].Kind; TrueFiles = @($files) })
    }
    [System.IO.File]::WriteAllText((Join-Path $Work "queries.json"), (ConvertTo-Json -InputObject @($queries) -Depth 4), $utf8NoBom)
    [System.IO.File]::WriteAllText((Join-Path $gramFolder "meta.json"), (ConvertTo-Json -InputObject ([ordered]@{ UnitCount = $sources.Count; BlockCounts = $blockCounts.ToArray() }) -Depth 4), $utf8NoBom)

    writeResult "prep_$Dataset" ([ordered]@{
            Type            = "prep"
            Dataset         = $Dataset
            Scale           = $Scale
            Files           = $sources.Count
            TotalChars      = $chars
            BlockChars      = $BlockChars
            Blocks          = $blockSizes.Count
            GramSeconds     = [Math]::Round($gramSeconds, 1)
            TruthSeconds    = [Math]::Round($truthTimer.Elapsed.TotalSeconds, 1)
            FileDistinct    = getStats @($results | ForEach-Object { $_.Distinct })
            BlockDistinct   = getStats $blockSizes
            TotalSeconds    = [Math]::Round($totalTimer.Elapsed.TotalSeconds, 1)
            PeakMegabytes   = getPeakMegabytes
        })
}

# ---------------------------------------------------------------- build（表を作る）

function loadUnitGrams {
    param ([string]$unitKind)
    $meta = ConvertFrom-Json ([System.IO.File]::ReadAllText((Join-Path $gramFolder "meta.json"), $utf8NoBom))
    $grams = New-Object 'System.Collections.Generic.List[uint32[]]'
    $unitFile = New-Object 'System.Collections.Generic.List[int]'
    for ($fileIndex = 0; $fileIndex -lt $meta.UnitCount; $fileIndex++) {
        if ($unitKind -eq "files") {
            $grams.Add((readWholeUInt32 (Join-Path $gramFolder "files_$fileIndex.u32")))
            $unitFile.Add($fileIndex)
        } else {
            $bytes = [System.IO.File]::ReadAllBytes((Join-Path $gramFolder "blocks_$fileIndex.bin"))
            $position = 0
            while ($position -lt $bytes.Length) {
                $count = [System.BitConverter]::ToInt32($bytes, $position)
                $position += 4
                $values = New-Object 'uint32[]' $count
                [System.Buffer]::BlockCopy($bytes, $position, $values, 0, $count * 4)
                $position += $count * 4
                $grams.Add($values)
                $unitFile.Add($fileIndex)
            }
        }
    }
    if ($grams.Count -ge 65535) { throw "単位が多すぎます（uint16 に収まりません）" }
    return @{ Grams = $grams; UnitFile = $unitFile.ToArray(); FileCount = [int]$meta.UnitCount }
}

function buildParts {
    # gather: 値の範囲 [low, high) の (gram, 単位の番号) の組を keys / items に並べて返す。ここで並べ替え、gram ごとにまとめ、shape の形で書く
    param ($dict, [int]$parts, [int]$unitTotal, [int]$unitCountForThreshold, [string]$shape, [string]$folder, $gather)
    [void][System.IO.Directory]::CreateDirectory($folder)
    $stride = [int][Math]::Ceiling($unitTotal / 8.0)
    $parts = [Math]::Max(1, [Math]::Min($parts, $dict.Length))
    $cuts = New-Object 'int[]' ($parts + 1)
    for ($partIndex = 0; $partIndex -le $parts; $partIndex++) { $cuts[$partIndex] = [int][Math]::Floor([double]$dict.Length * $partIndex / $parts) }

    $dictStream = [System.IO.File]::Create((Join-Path $folder "dict.bin"), 1MB)
    $offsetStream = $null; $listStream = $null; $rowStream = $null; $heavyDictStream = $null
    if ($shape -ne "bitset") {
        $offsetStream = [System.IO.File]::Create((Join-Path $folder "offs.bin"), 1MB)
        $listStream = [System.IO.File]::Create((Join-Path $folder "lists.bin"), 1MB)
    }
    if ($shape -ne "list") { $rowStream = [System.IO.File]::Create((Join-Path $folder "rows.bin"), 1MB) }
    if ($shape -eq "mixed") { $heavyDictStream = [System.IO.File]::Create((Join-Path $folder "hdict.bin"), 1MB) }

    $times = @{ Gather = 0.0; Sort = 0.0; Group = 0.0; Shape = 0.0; Write = 0.0 }
    $histogram = New-Object 'long[]' 6
    $rowTotal = [long]0
    $lightRows = [long]0
    $heavyGrams = [long]0
    $topCount = 0
    $topGram = [uint32]0
    $timer = [System.Diagnostics.Stopwatch]::new()

    for ($partIndex = 0; $partIndex -lt $parts; $partIndex++) {
        $groupCount = $cuts[$partIndex + 1] - $cuts[$partIndex]
        if ($groupCount -le 0) { continue }
        $dictBase = $cuts[$partIndex]
        $lowValue = $dict[$dictBase]
        $highValue = if ($partIndex -lt $parts - 1) { $dict[$cuts[$partIndex + 1]] } else { [uint32]0 }

        $timer.Restart()
        $part = & $gather $lowValue $highValue ($partIndex -eq 0) ($partIndex -eq $parts - 1)
        $keys = $part.GramKeys; $items = $part.Items; $rowCount = $part.RowCount
        $times.Gather += $timer.Elapsed.TotalSeconds

        $timer.Restart()
        [Array]::Sort($keys, $items)
        $times.Sort += $timer.Elapsed.TotalSeconds

        # gram ごとの行数（bitset は同じ走査でビットも立てる）
        $timer.Restart()
        $counts = New-Object 'int[]' $groupCount
        $bits = $null
        if ($shape -eq "bitset") { $bits = New-Object byte[] ($groupCount * $stride) }
        $groupIndex = 0
        $current = $dict[$dictBase]
        $rowBase = 0
        $groupRows = 0
        if ($shape -eq "bitset") {
            for ($rowIndex = 0; $rowIndex -lt $rowCount; $rowIndex++) {
                if ($keys[$rowIndex] -ne $current) {
                    $counts[$groupIndex] = $groupRows
                    $groupIndex++
                    $current = $dict[$dictBase + $groupIndex]
                    $groupRows = 0
                    $rowBase = $groupIndex * $stride
                }
                $groupRows++
                $unitId = [int]$items[$rowIndex]
                $bytePosition = $rowBase + ($unitId -shr 3)
                $bits[$bytePosition] = $bits[$bytePosition] -bor $bitMasks[$unitId -band 7]
            }
        } else {
            for ($rowIndex = 0; $rowIndex -lt $rowCount; $rowIndex++) {
                if ($keys[$rowIndex] -ne $current) {
                    $counts[$groupIndex] = $groupRows
                    $groupIndex++
                    $current = $dict[$dictBase + $groupIndex]
                    $groupRows = 0
                }
                $groupRows++
            }
        }
        $counts[$groupIndex] = $groupRows
        if ($groupIndex + 1 -ne $groupCount) { throw "gram の数が合いません（$($groupIndex + 1) と $groupCount）" }
        $keys = $null
        $times.Group += $timer.Elapsed.TotalSeconds

        $timer.Restart()
        $heavyFlags = $null
        for ($groupIndex = 0; $groupIndex -lt $groupCount; $groupIndex++) {
            $count = $counts[$groupIndex]
            $bucket = if ($count -eq 1) { 0 } elseif ($count -le 3) { 1 } elseif ($count -le 15) { 2 } elseif ($count * 16 -le $unitCountForThreshold) { 3 } elseif ($count * 2 -le $unitCountForThreshold) { 4 } else { 5 }
            $histogram[$bucket]++
            if ($count -gt $topCount) { $topCount = $count; $topGram = $dict[$dictBase + $groupIndex] }
        }
        $times.Group += $timer.Elapsed.TotalSeconds

        # shape ごとの出力の材料
        $timer.Restart()
        $offsets = $null; $lightItems = $null; $lightDict = $null; $heavyDict = $null; $heavyRows = $null
        $lightGroupCount = 0; $lightRowCount = 0; $heavyCount = 0
        if ($shape -eq "list") {
            $offsets = New-Object 'uint32[]' $groupCount
            $running = $lightRows
            for ($groupIndex = 0; $groupIndex -lt $groupCount; $groupIndex++) {
                $offsets[$groupIndex] = $running
                $running += $counts[$groupIndex]
            }
            $lightGroupCount = $groupCount
            $lightRowCount = $rowCount
            $lightItems = $items
        } elseif ($shape -eq "mixed") {
            for ($groupIndex = 0; $groupIndex -lt $groupCount; $groupIndex++) {
                if ($counts[$groupIndex] * 16 -gt $unitCountForThreshold) { $heavyCount++ } else { $lightRowCount += $counts[$groupIndex] }
            }
            $lightGroupCount = $groupCount - $heavyCount
            $lightItems = New-Object 'uint16[]' $lightRowCount
            $lightDict = New-Object 'uint32[]' $lightGroupCount
            $offsets = New-Object 'uint32[]' $lightGroupCount
            $heavyDict = New-Object 'uint32[]' $heavyCount
            $heavyRows = New-Object byte[] ($heavyCount * $stride)
            $lightIndex = 0; $heavyIndex = 0; $lightPosition = 0; $start = 0
            for ($groupIndex = 0; $groupIndex -lt $groupCount; $groupIndex++) {
                $count = $counts[$groupIndex]
                if ($count * 16 -gt $unitCountForThreshold) {
                    $heavyDict[$heavyIndex] = $dict[$dictBase + $groupIndex]
                    $heavyBase = $heavyIndex * $stride
                    $end = $start + $count
                    for ($rowIndex = $start; $rowIndex -lt $end; $rowIndex++) {
                        $unitId = [int]$items[$rowIndex]
                        $bytePosition = $heavyBase + ($unitId -shr 3)
                        $heavyRows[$bytePosition] = $heavyRows[$bytePosition] -bor $bitMasks[$unitId -band 7]
                    }
                    $heavyIndex++
                } else {
                    [System.Buffer]::BlockCopy($items, $start * 2, $lightItems, $lightPosition * 2, $count * 2)
                    $lightDict[$lightIndex] = $dict[$dictBase + $groupIndex]
                    $offsets[$lightIndex] = $lightRows + $lightPosition
                    $lightIndex++
                    $lightPosition += $count
                }
                $start += $count
            }
        }
        $times.Shape += $timer.Elapsed.TotalSeconds

        $timer.Restart()
        if ($shape -eq "list") {
            writeArraySlice $dictStream $dict 4 $dictBase $groupCount
            writeArraySlice $offsetStream $offsets 4 0 $groupCount
            writeArraySlice $listStream $lightItems 2 0 $rowCount
            $lightRows += $rowCount
        } elseif ($shape -eq "bitset") {
            writeArraySlice $dictStream $dict 4 $dictBase $groupCount
            $dictStream.Flush()
            writeArraySlice $rowStream $bits 1 0 ($groupCount * $stride)
        } else {
            writeArraySlice $dictStream $lightDict 4 0 $lightGroupCount
            writeArraySlice $offsetStream $offsets 4 0 $lightGroupCount
            writeArraySlice $listStream $lightItems 2 0 $lightRowCount
            writeArraySlice $heavyDictStream $heavyDict 4 0 $heavyCount
            writeArraySlice $rowStream $heavyRows 1 0 ($heavyCount * $stride)
            $lightRows += $lightRowCount
            $heavyGrams += $heavyCount
        }
        $times.Write += $timer.Elapsed.TotalSeconds
        $rowTotal += $rowCount
        $items = $null; $counts = $null; $bits = $null; $lightItems = $null; $offsets = $null; $heavyRows = $null
    }

    if ($shape -ne "bitset") {
        $last = New-Object 'uint32[]' 1
        $last[0] = $lightRows
        writeArraySlice $offsetStream $last 4 0 1
    }
    foreach ($stream in @($dictStream, $offsetStream, $listStream, $rowStream, $heavyDictStream)) {
        if ($null -ne $stream) { $stream.Dispose() }
    }
    $sizes = [ordered]@{}
    $total = [long]0
    foreach ($file in [System.IO.Directory]::GetFiles($folder)) {
        $length = ([System.IO.FileInfo]$file).Length
        $sizes[[System.IO.Path]::GetFileName($file)] = $length
        $total += $length
    }
    return [ordered]@{
        Grams         = $dict.Length
        Rows          = $rowTotal
        HeavyGrams    = $heavyGrams
        Parts         = $parts
        Sizes         = $sizes
        TotalBytes    = $total
        Histogram     = [ordered]@{ "1 ファイル" = $histogram[0]; "2〜3" = $histogram[1]; "4〜15" = $histogram[2]; "16〜全体の1/16" = $histogram[3]; "1/16〜1/2" = $histogram[4]; "1/2 超" = $histogram[5] }
        TopWord       = convertGramToText $topGram
        TopCount      = $topCount
        GatherSeconds = [Math]::Round($times.Gather, 1)
        SortSeconds   = [Math]::Round($times.Sort, 1)
        GroupSeconds  = [Math]::Round($times.Group, 1)
        ShapeSeconds  = [Math]::Round($times.Shape, 1)
        WriteSeconds  = [Math]::Round($times.Write, 1)
    }
}

function newGramDictionary {
    param ($gramLists)
    $gramSet = New-Object 'System.Collections.Generic.HashSet[uint32]'
    foreach ($values in $gramLists) { $gramSet.UnionWith($values) }
    $dict = New-Object 'uint32[]' $gramSet.Count
    $gramSet.CopyTo($dict)
    [Array]::Sort($dict)
    return , $dict
}

function newGramGather {
    # 単位ごとの 2-gram の配列（昇順・重複なし）から、値の範囲の組を並べる口
    param ($gramLists, [int[]]$unitIds)
    $lowerBound = ${function:getLowerBound}
    $repeatFill = ${function:fillRepeated}
    return {
        param ([uint32]$lowValue, [uint32]$highValue, [bool]$isFirst, [bool]$isLast)
        $unitCount = $gramLists.Count
        $froms = New-Object 'int[]' $unitCount
        $tos = New-Object 'int[]' $unitCount
        $rowCount = 0
        for ($unitIndex = 0; $unitIndex -lt $unitCount; $unitIndex++) {
            $values = $gramLists[$unitIndex]
            $froms[$unitIndex] = if ($isFirst) { 0 } else { & $lowerBound $values $lowValue }
            $tos[$unitIndex] = if ($isLast) { $values.Length } else { & $lowerBound $values $highValue }
            $rowCount += $tos[$unitIndex] - $froms[$unitIndex]
        }
        $keys = New-Object 'uint32[]' $rowCount
        $items = New-Object 'uint16[]' $rowCount
        $position = 0
        for ($unitIndex = 0; $unitIndex -lt $unitCount; $unitIndex++) {
            $length = $tos[$unitIndex] - $froms[$unitIndex]
            if ($length -le 0) { continue }
            [System.Buffer]::BlockCopy($gramLists[$unitIndex], $froms[$unitIndex] * 4, $keys, $position * 4, $length * 4)
            $items[$position] = [uint16]$unitIds[$unitIndex]
            & $repeatFill $items $position $length 2
            $position += $length
        }
        return @{ GramKeys = $keys; Items = $items; RowCount = $rowCount }
    }.GetNewClosure()
}

function invokeBuild {
    $totalTimer = [System.Diagnostics.Stopwatch]::StartNew()
    $timer = [System.Diagnostics.Stopwatch]::StartNew()
    $loaded = loadUnitGrams $Unit
    $loadSeconds = $timer.Elapsed.TotalSeconds
    # 最大メモリの中身を見るための途中の値（GC をかけたあとの、管理されたメモリの大きさ）。全ファイルの gram の配列がどれだけを占めるか
    $managedAfterLoad = [Math]::Round([GC]::GetTotalMemory($true) / 1MB)
    $peakAfterLoad = getPeakMegabytes
    $timer.Restart()
    $dict = newGramDictionary $loaded.Grams
    $dictSeconds = $timer.Elapsed.TotalSeconds
    $peakAfterDictionary = getPeakMegabytes
    $managedAfterDictionary = [Math]::Round([GC]::GetTotalMemory($true) / 1MB)
    $unitIds = [int[]](0..($loaded.Grams.Count - 1))
    $gather = newGramGather $loaded.Grams $unitIds
    $metrics = buildParts $dict $Parts $loaded.Grams.Count $loaded.Grams.Count $Shape $shapeFolder $gather
    # 単位 -> ファイルの対応（ブロックのとき必要）
    $map = New-Object 'uint16[]' $loaded.UnitFile.Length
    for ($unitIndex = 0; $unitIndex -lt $map.Length; $unitIndex++) { $map[$unitIndex] = [uint16]$loaded.UnitFile[$unitIndex] }
    $stream = [System.IO.File]::Create((Join-Path $shapeFolder "unitfile.bin"))
    writeArraySlice $stream $map 2 0 $map.Length
    $stream.Dispose()
    $metrics.Type = "build"
    $metrics.Dataset = $Dataset
    $metrics.Shape = $Shape
    $metrics.Unit = $Unit
    $metrics.Label = $Label
    $metrics.Units = $loaded.Grams.Count
    $metrics.ManagedMegabytesAfterLoad = $managedAfterLoad
    $metrics.PeakMegabytesAfterLoad = $peakAfterLoad
    $metrics.ManagedMegabytesAfterDictionary = $managedAfterDictionary
    $metrics.PeakMegabytesAfterDictionary = $peakAfterDictionary
    $metrics.LoadSeconds = [Math]::Round($loadSeconds, 1)
    $metrics.DictSeconds = [Math]::Round($dictSeconds, 1)
    $metrics.TotalSeconds = [Math]::Round($totalTimer.Elapsed.TotalSeconds, 1)
    $metrics.PeakMegabytes = getPeakMegabytes
    writeResult "build_${Dataset}_${Shape}_${Unit}$Label" $metrics
}

# ---------------------------------------------------------------- search（表を引く）

function addUnitsToCounts {
    param ($counts, $items)
    foreach ($item in $items) { $counts[$item]++ }
}

function getCandidates {
    param ($counts, [int]$needed)
    $candidates = New-Object 'System.Collections.Generic.List[int]'
    for ($unitIndex = 0; $unitIndex -lt $counts.Length; $unitIndex++) {
        if ($counts[$unitIndex] -eq $needed) { $candidates.Add($unitIndex) }
    }
    return , $candidates.ToArray()
}

function searchListFs {
    param ([string]$folder, $gramValues, [int]$unitTotal)
    $dictStream = openShared (Join-Path $folder "dict.bin")
    $offsetStream = openShared (Join-Path $folder "offs.bin")
    $listStream = openShared (Join-Path $folder "lists.bin")
    try {
        $dict = readUInt32Array $dictStream 0 ([int]($dictStream.Length / 4))
        $counts = New-Object byte[] $unitTotal
        foreach ($gram in $gramValues) {
            $found = [Array]::BinarySearch($dict, $gram)
            if ($found -lt 0) { return , ([int[]]@()) }
            $range = readUInt32Array $offsetStream ([long]$found * 4) 2
            $items = readUInt16Array $listStream ([long]$range[0] * 2) ([int]($range[1] - $range[0]))
            addUnitsToCounts $counts $items
        }
        return , (getCandidates $counts $gramValues.Length)
    } finally {
        $dictStream.Dispose(); $offsetStream.Dispose(); $listStream.Dispose()
    }
}

function readUInt32At {
    param ($stream, [long]$position, $buffer)
    [void]$stream.Seek($position, [System.IO.SeekOrigin]::Begin)
    $done = 0
    while ($done -lt 4) {
        $read = $stream.Read($buffer, $done, 4 - $done)
        if ($read -le 0) { throw "ファイルが途中で終わっています" }
        $done += $read
    }
    return [System.BitConverter]::ToUInt32($buffer, 0)
}

function searchListFsSeek {
    # FileStream で、辞書を丸ごと読まずに、位置を指定して二分探索する（1 回の探索で 4 バイトの読み込みを約 24 回）
    param ([string]$folder, $gramValues, [int]$unitTotal)
    $dictStream = openShared (Join-Path $folder "dict.bin")
    $offsetStream = openShared (Join-Path $folder "offs.bin")
    $listStream = openShared (Join-Path $folder "lists.bin")
    try {
        $dictCount = [long]($dictStream.Length / 4)
        $buffer = New-Object byte[] 4
        $counts = New-Object byte[] $unitTotal
        foreach ($gram in $gramValues) {
            $lowIndex = [long]0; $highIndex = $dictCount - 1; $found = -1
            while ($lowIndex -le $highIndex) {
                $middle = [long][Math]::Floor(($lowIndex + $highIndex) / 2)
                $value = readUInt32At $dictStream ($middle * 4) $buffer
                if ($value -eq $gram) { $found = $middle; break }
                if ($value -lt $gram) { $lowIndex = $middle + 1 } else { $highIndex = $middle - 1 }
            }
            if ($found -lt 0) { return , ([int[]]@()) }
            $range = readUInt32Array $offsetStream ([long]$found * 4) 2
            $items = readUInt16Array $listStream ([long]$range[0] * 2) ([int]($range[1] - $range[0]))
            addUnitsToCounts $counts $items
        }
        return , (getCandidates $counts $gramValues.Length)
    } finally {
        $dictStream.Dispose(); $offsetStream.Dispose(); $listStream.Dispose()
    }
}

function searchListMmf {
    # 開いたファイルを MemoryMappedFile にして、辞書を二分探索する（辞書の全体は読まない）。ReadUInt32 / ReadUInt16 を PowerShell から 1 回ずつ呼ぶ
    param ([string]$folder, $gramValues, [int]$unitTotal)
    $names = @("dict.bin", "offs.bin", "lists.bin")
    $streams = @{}; $mappings = @{}; $views = @{}
    try {
        foreach ($name in $names) {
            $streams[$name] = openShared (Join-Path $folder $name)
            if ($streams[$name].Length -eq 0) { return , ([int[]]@()) }
            $mappings[$name] = [System.IO.MemoryMappedFiles.MemoryMappedFile]::CreateFromFile($streams[$name], [NullString]::Value, 0, [System.IO.MemoryMappedFiles.MemoryMappedFileAccess]::Read, [System.IO.HandleInheritability]::None, $true)
            $views[$name] = $mappings[$name].CreateViewAccessor(0, 0, [System.IO.MemoryMappedFiles.MemoryMappedFileAccess]::Read)
        }
        $dictCount = [long]($streams["dict.bin"].Length / 4)
        $counts = New-Object byte[] $unitTotal
        foreach ($gram in $gramValues) {
            $lowIndex = [long]0; $highIndex = $dictCount - 1; $found = -1
            while ($lowIndex -le $highIndex) {
                $middle = [long][Math]::Floor(($lowIndex + $highIndex) / 2)
                $value = $views["dict.bin"].ReadUInt32($middle * 4)
                if ($value -eq $gram) { $found = $middle; break }
                if ($value -lt $gram) { $lowIndex = $middle + 1 } else { $highIndex = $middle - 1 }
            }
            if ($found -lt 0) { return , ([int[]]@()) }
            $startRow = [long]$views["offs.bin"].ReadUInt32($found * 4)
            $endRow = [long]$views["offs.bin"].ReadUInt32($found * 4 + 4)
            for ($row = $startRow; $row -lt $endRow; $row++) { $counts[$views["lists.bin"].ReadUInt16($row * 2)]++ }
        }
        return , (getCandidates $counts $gramValues.Length)
    } finally {
        foreach ($view in $views.Values) { $view.Dispose() }
        foreach ($mapping in $mappings.Values) { $mapping.Dispose() }
        foreach ($stream in $streams.Values) { $stream.Dispose() }
    }
}

function searchBitsetFs {
    param ([string]$folder, $gramValues, [int]$unitTotal)
    $stride = [int][Math]::Ceiling($unitTotal / 8.0)
    $dictStream = openShared (Join-Path $folder "dict.bin")
    $rowStream = openShared (Join-Path $folder "rows.bin")
    try {
        $dict = readUInt32Array $dictStream 0 ([int]($dictStream.Length / 4))
        $counts = New-Object byte[] $unitTotal
        foreach ($gram in $gramValues) {
            $found = [Array]::BinarySearch($dict, $gram)
            if ($found -lt 0) { return , ([int[]]@()) }
            $row = readBytes $rowStream ([long]$found * $stride) $stride
            for ($unitIndex = 0; $unitIndex -lt $unitTotal; $unitIndex++) {
                if ($row[$unitIndex -shr 3] -band $bitMasks[$unitIndex -band 7]) { $counts[$unitIndex]++ }
            }
        }
        return , (getCandidates $counts $gramValues.Length)
    } finally {
        $dictStream.Dispose(); $rowStream.Dispose()
    }
}

function searchMixedFs {
    param ([string]$folder, $gramValues, [int]$unitTotal)
    $stride = [int][Math]::Ceiling($unitTotal / 8.0)
    $streams = @{}
    foreach ($name in @("dict.bin", "offs.bin", "lists.bin", "hdict.bin", "rows.bin")) { $streams[$name] = openShared (Join-Path $folder $name) }
    try {
        $dict = readUInt32Array $streams["dict.bin"] 0 ([int]($streams["dict.bin"].Length / 4))
        $heavyDict = readUInt32Array $streams["hdict.bin"] 0 ([int]($streams["hdict.bin"].Length / 4))
        $counts = New-Object byte[] $unitTotal
        foreach ($gram in $gramValues) {
            $heavyFound = [Array]::BinarySearch($heavyDict, $gram)
            if ($heavyFound -ge 0) {
                $row = readBytes $streams["rows.bin"] ([long]$heavyFound * $stride) $stride
                for ($unitIndex = 0; $unitIndex -lt $unitTotal; $unitIndex++) {
                    if ($row[$unitIndex -shr 3] -band $bitMasks[$unitIndex -band 7]) { $counts[$unitIndex]++ }
                }
                continue
            }
            $found = [Array]::BinarySearch($dict, $gram)
            if ($found -lt 0) { return , ([int[]]@()) }
            $range = readUInt32Array $streams["offs.bin"] ([long]$found * 4) 2
            $items = readUInt16Array $streams["lists.bin"] ([long]$range[0] * 2) ([int]($range[1] - $range[0]))
            addUnitsToCounts $counts $items
        }
        return , (getCandidates $counts $gramValues.Length)
    } finally {
        foreach ($stream in $streams.Values) { $stream.Dispose() }
    }
}

function getSearchQueries {
    param ($buildResult)
    $queries = New-Object System.Collections.ArrayList
    $fromFile = ConvertFrom-Json ([System.IO.File]::ReadAllText((Join-Path $Work "queries.json"), $utf8NoBom))
    foreach ($query in @($fromFile)) { [void]$queries.Add([pscustomobject]@{ Word = $query.Word; Kind = $query.Kind; TrueFiles = @($query.TrueFiles); HasTruth = $true }) }
    if ($buildResult -and $buildResult.TopWord) {
        [void]$queries.Add([pscustomobject]@{ Word = $buildResult.TopWord; Kind = "top"; TrueFiles = @(); HasTruth = $false })
    }
    return , $queries.ToArray()
}

function measureQueries {
    # search: クエリごとに「最初の 1 回」と「繰り返し -Repeat 回の中央値」を測り、真に含むファイルを漏らしていないか確かめる
    param ($queries, [scriptblock]$invokeSearch, $unitFile)
    $rows = New-Object System.Collections.ArrayList
    $processFirstMs = $null
    foreach ($query in $queries) {
        $grams = getSearchGramValues $query.Word
        if ($grams.Length -eq 0) { continue }
        $timer = [System.Diagnostics.Stopwatch]::StartNew()
        $candidates = & $invokeSearch $grams
        $firstMs = $timer.Elapsed.TotalMilliseconds
        if ($null -eq $processFirstMs) { $processFirstMs = $firstMs }
        $samples = New-Object 'System.Collections.Generic.List[double]'
        for ($count = 0; $count -lt $Repeat; $count++) {
            $timer.Restart()
            [void](& $invokeSearch $grams)
            $samples.Add($timer.Elapsed.TotalMilliseconds)
        }
        $candidateFiles = New-Object 'System.Collections.Generic.HashSet[int]'
        foreach ($candidate in $candidates) { [void]$candidateFiles.Add($(if ($null -ne $unitFile) { [int]$unitFile[$candidate] } else { [int]$candidate })) }
        $missing = 0
        foreach ($trueFile in $query.TrueFiles) { if (!$candidateFiles.Contains([int]$trueFile)) { $missing++ } }
        [void]$rows.Add([pscustomobject]@{
                Word = $query.Word; Kind = $query.Kind; Grams = $grams.Length
                Units = @($candidates).Count; Files = $candidateFiles.Count; TrueFiles = @($query.TrueFiles).Count; Missing = $missing
                FirstMs = [Math]::Round($firstMs, 2); MedianMs = [Math]::Round((getStats $samples).Median, 2)
            })
    }
    return @{ Rows = $rows.ToArray(); ProcessFirstMs = [Math]::Round($processFirstMs, 2) }
}

function summarizeQueryRows {
    param ($rows)
    $summary = [ordered]@{}
    foreach ($group in ($rows | Group-Object Kind)) {
        $summary[$group.Name] = [ordered]@{
            Queries    = $group.Count
            Units      = getStats @($group.Group | ForEach-Object { $_.Units })
            Files      = getStats @($group.Group | ForEach-Object { $_.Files })
            TrueFiles  = getStats @($group.Group | ForEach-Object { $_.TrueFiles })
            MedianMs   = getStats @($group.Group | ForEach-Object { $_.MedianMs })
            FirstMs    = getStats @($group.Group | ForEach-Object { $_.FirstMs })
            Missing    = [int](($group.Group | Measure-Object Missing -Sum).Sum)
        }
    }
    return $summary
}

function invokeSearch {
    $buildResult = readResult "build_${Dataset}_${Shape}_${Unit}$Label"
    $queries = getSearchQueries $buildResult
    $unitFile = readWholeUInt16 (Join-Path $shapeFolder "unitfile.bin")
    $unitTotal = $unitFile.Length
    $methods = @("fs")
    if ($Shape -eq "list") { $methods += "fsseek"; $methods += "mmf" }
    $results = [ordered]@{}
    foreach ($method in $methods) {
        $folder = $shapeFolder
        $invoke = switch ("${Shape}_${method}") {
            "list_fs" { $search = ${function:searchListFs}; { param ($grams) & $search $folder $grams $unitTotal }.GetNewClosure() }
            "list_fsseek" { $search = ${function:searchListFsSeek}; { param ($grams) & $search $folder $grams $unitTotal }.GetNewClosure() }
            "list_mmf" { $search = ${function:searchListMmf}; { param ($grams) & $search $folder $grams $unitTotal }.GetNewClosure() }
            "bitset_fs" { $search = ${function:searchBitsetFs}; { param ($grams) & $search $folder $grams $unitTotal }.GetNewClosure() }
            "mixed_fs" { $search = ${function:searchMixedFs}; { param ($grams) & $search $folder $grams $unitTotal }.GetNewClosure() }
        }
        $measured = measureQueries $queries $invoke $(if ($Unit -eq "blocks") { $unitFile } else { $null })
        $results[$method] = [ordered]@{ ProcessFirstMs = $measured.ProcessFirstMs; ByKind = summarizeQueryRows $measured.Rows }
    }
    writeResult "search_${Dataset}_${Shape}_${Unit}$Label" ([ordered]@{ Type = "search"; Dataset = $Dataset; Shape = $Shape; Unit = $Unit; Methods = $results; PeakMegabytes = getPeakMegabytes })
}

# ---------------------------------------------------------------- 区画（segment）と、まとめ直し

function invokeSegmentBuild {
    # 土台（先頭の単位）+ 末尾の 7 単位を 1 つずつの区画にする。1 ブック分（1 ファイルの gram の 1/100）の区画も作る
    $loaded = loadUnitGrams "files"
    $total = $loaded.Grams.Count
    $segmentUnits = [Math]::Min(7, $total - 1)
    $timer = [System.Diagnostics.Stopwatch]::StartNew()
    $baseGrams = New-Object 'System.Collections.Generic.List[uint32[]]'
    $baseIds = New-Object 'System.Collections.Generic.List[int]'
    for ($unitIndex = 0; $unitIndex -lt $total - $segmentUnits; $unitIndex++) { $baseGrams.Add($loaded.Grams[$unitIndex]); $baseIds.Add($unitIndex) }
    $baseDict = newGramDictionary $baseGrams
    [void](buildParts $baseDict $Parts $total $total "list" (Join-Path $Work "seg_base") (newGramGather $baseGrams $baseIds.ToArray()))
    $baseSeconds = $timer.Elapsed.TotalSeconds

    $segmentSeconds = New-Object 'System.Collections.Generic.List[double]'
    for ($segmentIndex = 1; $segmentIndex -le $segmentUnits; $segmentIndex++) {
        $unitIndex = $total - $segmentUnits + $segmentIndex - 1
        $timer.Restart()
        $single = New-Object 'System.Collections.Generic.List[uint32[]]'
        $single.Add($loaded.Grams[$unitIndex])
        $singleDict = newGramDictionary $single
        [void](buildParts $singleDict 1 $total $total "list" (Join-Path $Work "seg_$segmentIndex") (newGramGather $single @($unitIndex)))
        $segmentSeconds.Add($timer.Elapsed.TotalSeconds)
    }
    # 1 ブックの取り込み: 1 ファイルの gram のうち 1/100（値の範囲で切り出したもの）の区画
    $timer.Restart()
    $whole = $loaded.Grams[$total - 1]
    $slice = New-Object 'uint32[]' ([Math]::Max(1, [int]($whole.Length / 100)))
    [System.Buffer]::BlockCopy($whole, 0, $slice, 0, $slice.Length * 4)
    $sliceList = New-Object 'System.Collections.Generic.List[uint32[]]'
    $sliceList.Add($slice)
    $sliceDict = newGramDictionary $sliceList
    [void](buildParts $sliceDict 1 $total $total "list" (Join-Path $Work "seg_book") (newGramGather $sliceList @(($total - 1))))
    $bookSeconds = $timer.Elapsed.TotalSeconds

    # 書き直しの区画: 0 番のファイルを書き直したとして、元の gram の前半を無くし、新しい gram（私用領域の文字の 2 文字の組 1000 個）を足した区画
    $timer.Restart()
    $original = $loaded.Grams[0]
    $half = [int]($original.Length / 2)
    $rewritten = New-Object 'uint32[]' ($original.Length - $half + 1000)
    [System.Buffer]::BlockCopy($original, $half * 4, $rewritten, 0, ($original.Length - $half) * 4)
    for ($newIndex = 0; $newIndex -lt 1000; $newIndex++) {
        $rewritten[$original.Length - $half + $newIndex] = [uint32](0xE000 + $newIndex) + 65536 * [uint32](0xE000 + $newIndex + 1)
    }
    $rewriteList = New-Object 'System.Collections.Generic.List[uint32[]]'
    $rewriteList.Add($rewritten)
    $rewriteDict = newGramDictionary $rewriteList
    [void](buildParts $rewriteDict 1 $total $total "list" (Join-Path $Work "seg_rewrite") (newGramGather $rewriteList @(0)))
    $rewriteSeconds = $timer.Elapsed.TotalSeconds

    writeResult "segbuild_$Dataset" ([ordered]@{
            Type = "segbuild"; Dataset = $Dataset; Units = $total; SegmentUnits = $segmentUnits
            BaseSeconds = [Math]::Round($baseSeconds, 1)
            OneFileSegmentSeconds = getStats $segmentSeconds
            OneBookSegmentSeconds = [Math]::Round($bookSeconds, 2); OneBookGrams = $slice.Length
            RewriteSegmentSeconds = [Math]::Round($rewriteSeconds, 2); RewriteGrams = $rewritten.Length
            PeakMegabytes = getPeakMegabytes
        })
}

function loadSegment {
    param ([string]$folder)
    return @{
        Dict  = readWholeUInt32 (Join-Path $folder "dict.bin")
        Offs  = readWholeUInt32 (Join-Path $folder "offs.bin")
        Lists = readWholeUInt16 (Join-Path $folder "lists.bin")
    }
}

function newMergeGather {
    # 区画（list 形）の gram -> 単位の並びを、値の範囲ごとに (gram, 単位) の組に戻す口
    param ($segments)
    $lowerBound = ${function:getLowerBound}
    $repeatFill = ${function:fillRepeated}
    return {
        param ([uint32]$lowValue, [uint32]$highValue, [bool]$isFirst, [bool]$isLast)
        $rowCount = 0
        $ranges = New-Object System.Collections.ArrayList
        foreach ($segment in $segments) {
            $groupFrom = if ($isFirst) { 0 } else { & $lowerBound $segment.Dict $lowValue }
            $groupTo = if ($isLast) { $segment.Dict.Length } else { & $lowerBound $segment.Dict $highValue }
            $rowFrom = [int]$segment.Offs[$groupFrom]
            $rowTo = [int]$segment.Offs[$groupTo]
            $rowCount += $rowTo - $rowFrom
            [void]$ranges.Add(@($groupFrom, $groupTo, $rowFrom, $rowTo))
        }
        $keys = New-Object 'uint32[]' $rowCount
        $items = New-Object 'uint16[]' $rowCount
        $position = 0
        for ($segmentIndex = 0; $segmentIndex -lt $segments.Count; $segmentIndex++) {
            $segment = $segments[$segmentIndex]
            $range = $ranges[$segmentIndex]
            $dictValues = $segment.Dict
            $offs = $segment.Offs
            for ($groupIndex = $range[0]; $groupIndex -lt $range[1]; $groupIndex++) {
                $count = [int]($offs[$groupIndex + 1] - $offs[$groupIndex])
                $keys[$position] = $dictValues[$groupIndex]
                if ($count -gt 1) {
                    if ($count -lt 8) { for ($row = 1; $row -lt $count; $row++) { $keys[$position + $row] = $dictValues[$groupIndex] } }
                    else { & $repeatFill $keys $position $count 4 }
                }
                $position += $count
            }
            $rowLength = $range[3] - $range[2]
            if ($rowLength -gt 0) { [System.Buffer]::BlockCopy($segment.Lists, $range[2] * 2, $items, ($position - $rowLength) * 2, $rowLength * 2) }
        }
        return @{ GramKeys = $keys; Items = $items; RowCount = $rowCount }
    }.GetNewClosure()
}

function invokeMerge {
    $total = (ConvertFrom-Json ([System.IO.File]::ReadAllText((Join-Path $gramFolder "meta.json"), $utf8NoBom))).UnitCount
    $folders = New-Object 'System.Collections.Generic.List[string]'
    $folders.Add((Join-Path $Work "seg_base"))
    for ($segmentIndex = 1; $segmentIndex -lt $SegmentCount; $segmentIndex++) {
        $folder = Join-Path $Work "seg_$segmentIndex"
        if ([System.IO.Directory]::Exists($folder)) { $folders.Add($folder) }
    }
    $timer = [System.Diagnostics.Stopwatch]::StartNew()
    $segments = New-Object System.Collections.ArrayList
    foreach ($folder in $folders) { [void]$segments.Add((loadSegment $folder)) }
    $loadSeconds = $timer.Elapsed.TotalSeconds
    $dictLists = New-Object 'System.Collections.Generic.List[uint32[]]'
    foreach ($segment in $segments) { $dictLists.Add($segment.Dict) }
    $dict = newGramDictionary $dictLists
    $metrics = buildParts $dict $Parts $total $total "list" (Join-Path $Work "merged_$SegmentCount") (newMergeGather $segments)
    $metrics.Type = "merge"
    $metrics.Dataset = $Dataset
    $metrics.Segments = $folders.Count
    $metrics.LoadSeconds = [Math]::Round($loadSeconds, 1)
    $metrics.TotalSeconds = [Math]::Round($timer.Elapsed.TotalSeconds, 1)
    $metrics.PeakMegabytes = getPeakMegabytes
    writeResult "merge_${Dataset}_$SegmentCount" $metrics
}

function toIntList {
    param ($candidates)
    $list = New-Object 'System.Collections.Generic.List[int]'
    foreach ($candidate in $candidates) { $list.Add([int]$candidate) }
    return , $list
}

function invokeRewriteCheck {
    # 0 番のファイルを書き直した区画（seg_rewrite。元の gram の前半を無くし、新しい gram を足した）を一番新しい区画として足したときの、候補を確かめる。
    # 古い区画の 0 番のファイルの行を、新しい区画があるために無効にする規則（newest）と、無効にしない場合（naive）を比べる。
    param ($segmentFolders, [int]$total, [string]$wholeFolder)
    $rewriteFolder = Join-Path $Work "seg_rewrite"
    if (![System.IO.Directory]::Exists($rewriteFolder)) { return $null }
    $segmentUnits = [Math]::Min(7, $total - 1)
    $folders = New-Object 'System.Collections.Generic.List[string]'
    $covered = New-Object System.Collections.ArrayList
    $baseCovered = New-Object 'System.Collections.Generic.HashSet[int]'
    for ($unitIndex = 0; $unitIndex -lt $total - $segmentUnits; $unitIndex++) { [void]$baseCovered.Add($unitIndex) }
    $folders.Add($segmentFolders[0]); [void]$covered.Add($baseCovered)
    for ($segmentIndex = 1; $segmentIndex -le $segmentUnits; $segmentIndex++) {
        $folder = Join-Path $Work "seg_$segmentIndex"
        if (![System.IO.Directory]::Exists($folder)) { continue }
        $single = New-Object 'System.Collections.Generic.HashSet[int]'
        [void]$single.Add($total - $segmentUnits + $segmentIndex - 1)
        $folders.Add($folder); [void]$covered.Add($single)
    }
    $rewriteCovered = New-Object 'System.Collections.Generic.HashSet[int]'
    [void]$rewriteCovered.Add(0)
    $folders.Add($rewriteFolder); [void]$covered.Add($rewriteCovered)

    # 書き直す前に 0 番のファイルだけにあった gram（前半）を 2 文字の語にする
    $originalGrams = readWholeUInt32 (Join-Path $gramFolder "files_0.u32")
    $oldWords = New-Object System.Collections.ArrayList
    $searchMmf = ${function:searchListMmf}
    $searchList = ${function:searchListFs}
    $step = [Math]::Max(1, [int]($originalGrams.Length / 2 / 3000))
    for ($index = 0; $index -lt [int]($originalGrams.Length / 2) -and $oldWords.Count -lt 10; $index += $step) {
        $word = convertGramToText $originalGrams[$index]
        $roundTrip = getSearchGramValues $word
        if ($roundTrip.Length -ne 1 -or $roundTrip[0] -ne $originalGrams[$index]) { continue }
        $whole = toIntList (& $searchMmf $wholeFolder $roundTrip $total)
        if ($whole.Count -eq 1 -and $whole[0] -eq 0) { [void]$oldWords.Add($word) }
    }
    $newWords = New-Object System.Collections.ArrayList
    for ($newIndex = 0; $newIndex -lt 1000 -and $newWords.Count -lt 10; $newIndex += 100) {
        [void]$newWords.Add(([string][char](0xE000 + $newIndex)) + [char](0xE000 + $newIndex + 1) + [char](0xE000 + $newIndex + 2))
    }

    $result = [ordered]@{ OldWordCount = $oldWords.Count; NewWordCount = $newWords.Count; OldStaleNaive = 0; OldStaleNewest = 0; NewFoundNaive = 0; NewFoundNewest = 0 }
    foreach ($entry in @(@("old", $oldWords), @("new", $newWords))) {
        foreach ($word in $entry[1]) {
            $grams = getSearchGramValues $word
            $perFolder = New-Object System.Collections.ArrayList
            foreach ($folder in $folders) { [void]$perFolder.Add((toIntList (& $searchList $folder $grams $total))) }
            $naive = New-Object 'System.Collections.Generic.HashSet[int]'
            $newest = New-Object 'System.Collections.Generic.HashSet[int]'
            for ($folderIndex = 0; $folderIndex -lt $folders.Count; $folderIndex++) {
                foreach ($candidate in $perFolder[$folderIndex]) {
                    [void]$naive.Add([int]$candidate)
                    $replaced = $false
                    for ($laterIndex = $folderIndex + 1; $laterIndex -lt $folders.Count; $laterIndex++) { if ($covered[$laterIndex].Contains([int]$candidate)) { $replaced = $true; break } }
                    if (!$replaced) { [void]$newest.Add([int]$candidate) }
                }
            }
            if ($entry[0] -eq "old") {
                if ($naive.Contains(0)) { $result.OldStaleNaive++ }
                if ($newest.Contains(0)) { $result.OldStaleNewest++ }
            } else {
                if ($naive.Contains(0)) { $result.NewFoundNaive++ }
                if ($newest.Contains(0)) { $result.NewFoundNewest++ }
            }
        }
    }
    return $result
}

function invokeSegmentSearch {
    $buildResult = readResult "build_${Dataset}_list_files"
    $queries = getSearchQueries $buildResult
    $total = (ConvertFrom-Json ([System.IO.File]::ReadAllText((Join-Path $gramFolder "meta.json"), $utf8NoBom))).UnitCount
    $segmentFolders = New-Object 'System.Collections.Generic.List[string]'
    $segmentFolders.Add((Join-Path $Work "seg_base"))
    for ($segmentIndex = 1; $segmentIndex -le 7; $segmentIndex++) {
        $folder = Join-Path $Work "seg_$segmentIndex"
        if ([System.IO.Directory]::Exists($folder)) { $segmentFolders.Add($folder) }
    }
    $mergedFolder = Join-Path $Work "merged_$SegmentCount"
    $wholeFolder = Join-Path $Work "shape_list_files"
    $searchList = ${function:searchListFs}
    $invokeSegments = {
        param ($grams)
        $union = New-Object 'System.Collections.Generic.SortedSet[int]'
        foreach ($folder in $segmentFolders) { foreach ($candidate in (& $searchList $folder $grams $total)) { [void]$union.Add($candidate) } }
        return , ([int[]]@($union))
    }.GetNewClosure()
    $searchMmf = ${function:searchListMmf}
    $invokeSegmentsMmf = {
        param ($grams)
        $union = New-Object 'System.Collections.Generic.SortedSet[int]'
        foreach ($folder in $segmentFolders) { foreach ($candidate in (& $searchMmf $folder $grams $total)) { [void]$union.Add($candidate) } }
        return , ([int[]]@($union))
    }.GetNewClosure()
    $invokeMerged = { param ($grams) & $searchList $mergedFolder $grams $total }.GetNewClosure()
    $invokeMergedMmf = { param ($grams) & $searchMmf $mergedFolder $grams $total }.GetNewClosure()
    $invokeWhole = { param ($grams) & $searchList $wholeFolder $grams $total }.GetNewClosure()
    $results = [ordered]@{}
    foreach ($entry in @(@("whole", $invokeWhole), @("segments", $invokeSegments), @("merged", $invokeMerged), @("segments_mmf", $invokeSegmentsMmf), @("merged_mmf", $invokeMergedMmf))) {
        $measured = measureQueries $queries $entry[1] $null
        $results[$entry[0]] = [ordered]@{ ProcessFirstMs = $measured.ProcessFirstMs; ByKind = summarizeQueryRows $measured.Rows }
    }
    # 区画 8 つ・まとめ直し・全体を一度に作ったもので、候補が同じか
    $different = 0
    foreach ($query in $queries) {
        $grams = getSearchGramValues $query.Word
        if ($grams.Length -eq 0) { continue }
        $a = @(& $invokeSegments $grams); $b = @(& $invokeMerged $grams); $c = @(& $invokeWhole $grams)
        if (($a -join ",") -ne ($b -join ",") -or ($b -join ",") -ne ($c -join ",")) { $different++ }
    }
    $rewriteCheck = invokeRewriteCheck $segmentFolders $total $wholeFolder
    writeResult "segsearch_${Dataset}" ([ordered]@{ Type = "segsearch"; Dataset = $Dataset; Segments = $segmentFolders.Count; DifferentCandidates = $different; RewriteCheck = $rewriteCheck; Methods = $results; PeakMegabytes = getPeakMegabytes })
}

# ---------------------------------------------------------------- defender

function measureOpen {
    param ([string]$path)
    $times = [ordered]@{}
    foreach ($label in @("First", "Second")) {
        $timer = [System.Diagnostics.Stopwatch]::StartNew()
        $stream = openShared $path
        $openMs = $timer.Elapsed.TotalMilliseconds
        $buffer = New-Object byte[] 4MB
        while ($stream.Read($buffer, 0, $buffer.Length) -gt 0) { }
        $stream.Dispose()
        $times["${label}OpenMs"] = [Math]::Round($openMs, 1)
        $times["${label}ReadAllMs"] = [Math]::Round($timer.Elapsed.TotalMilliseconds, 1)
    }
    return $times
}

function invokeDefender {
    # Defender の設定は CI の実行機の上だけで読む（除外が残っていないかも記録する）
    $status = if (isCiRunner) { getDefenderState } else { [ordered]@{ Skipped = "CI の実行機ではないので読まない" } }
    $folder = Join-Path $Work "defender"
    [void][System.IO.Directory]::CreateDirectory($folder)
    $files = New-Object System.Collections.ArrayList
    $random = [System.Random]::new(3)
    foreach ($megabytes in @(50, 100, 200, 400)) {
        $path = Join-Path $folder "random_$megabytes.bin"
        $chunk = New-Object byte[] 1MB
        $writeTimer = [System.Diagnostics.Stopwatch]::StartNew()
        $stream = [System.IO.File]::Create($path)
        for ($count = 0; $count -lt $megabytes; $count++) { $random.NextBytes($chunk); $stream.Write($chunk, 0, $chunk.Length) }
        $stream.Dispose()
        $writeMs = $writeTimer.Elapsed.TotalMilliseconds
        $measured = measureOpen $path
        [void]$files.Add([ordered]@{ Name = "random_$megabytes"; Megabytes = $megabytes; WriteMs = [Math]::Round($writeMs, 1); First = $measured })
    }
    # 実際に作った表のファイル（作った後に別の段階を挟んでいるので、書いた直後ではない）
    foreach ($candidate in @("shape_list_files\lists.bin", "shape_bitset_files\rows.bin", "shape_list_blocks\lists.bin")) {
        $path = Join-Path $Work $candidate
        if ([System.IO.File]::Exists($path)) {
            $measured = measureOpen $path
            [void]$files.Add([ordered]@{ Name = $candidate; Megabytes = [Math]::Round(([System.IO.FileInfo]$path).Length / 1MB, 1); First = $measured })
        }
    }
    writeResult "defender_$Dataset" ([ordered]@{ Type = "defender"; Dataset = $Dataset; Status = $status; Files = $files.ToArray() })
}

# ---------------------------------------------------------------- defenderon（リアルタイム保護を有効にする試み）

function isCiRunner {
    return ($env:GITHUB_ACTIONS -eq "true" -and $env:RUNNER_ENVIRONMENT -eq "github-hosted")
}

function getDefenderState {
    try {
        $computer = Get-MpComputerStatus
        $preference = Get-MpPreference
        return [ordered]@{
            RealTimeProtectionEnabled = $computer.RealTimeProtectionEnabled
            AMServiceEnabled          = $computer.AMServiceEnabled
            AntivirusEnabled          = $computer.AntivirusEnabled
            DisableRealtimeMonitoring = $preference.DisableRealtimeMonitoring
            DisableIOAVProtection     = $preference.DisableIOAVProtection
            DisableBehaviorMonitoring = $preference.DisableBehaviorMonitoring
            ExclusionPath             = @($preference.ExclusionPath | ForEach-Object { [string]$_ })
            ExclusionExtension        = @($preference.ExclusionExtension | ForEach-Object { [string]$_ })
            ExclusionProcess          = @($preference.ExclusionProcess | ForEach-Object { [string]$_ })
        }
    } catch { return [ordered]@{ Error = $_.Exception.Message } }
}

function testExclusionCovers {
    # 除外の道（D:\ や D:\a など）が、調べるフォルダを含むか
    param ([string]$exclusion, [string]$target)
    $trimmed = $exclusion.TrimEnd('\')
    if ($trimmed.Length -eq 0) { return $false }
    return ($target.Equals($trimmed, [System.StringComparison]::OrdinalIgnoreCase) -or $target.StartsWith($trimmed + "\", [System.StringComparison]::OrdinalIgnoreCase))
}

function invokeDefenderOn {
    # CI の実行機の上だけで、保護を強める方向に変える（リアルタイム保護を有効にする・作業フォルダを含む除外を外す）。弱める方向の変更はしない。
    # 手元では設定を読みも書きもしない
    if (!(isCiRunner)) {
        writeResult "defenderon_$Dataset" ([ordered]@{ Type = "defenderon"; Dataset = $Dataset; Skipped = "CI の実行機ではないので何もしない" })
        return
    }
    $before = getDefenderState
    $message = ""
    try {
        Set-MpPreference -DisableRealtimeMonitoring $false -ErrorAction Stop
    } catch { $message = $_.Exception.Message }
    # 作業フォルダを含む除外（実行機の初期設定は D:\ と C:\ を除外している）を外す
    $target = [System.IO.Path]::GetFullPath($Work).TrimEnd('\')
    $removed = New-Object System.Collections.ArrayList
    $removeMessages = New-Object System.Collections.ArrayList
    if ($before.Contains("ExclusionPath")) {
        foreach ($exclusion in $before.ExclusionPath) {
            if (!(testExclusionCovers $exclusion $target)) { continue }
            try {
                Remove-MpPreference -ExclusionPath $exclusion -ErrorAction Stop
                [void]$removed.Add($exclusion)
            } catch { [void]$removeMessages.Add(("{0}: {1}" -f $exclusion, $_.Exception.Message)) }
        }
    }
    Start-Sleep -Seconds 5
    $after = getDefenderState
    $stillCovered = $null
    if ($after.Contains("ExclusionPath")) {
        $stillCovered = $false
        foreach ($exclusion in $after.ExclusionPath) { if (testExclusionCovers $exclusion $target) { $stillCovered = $true } }
    }
    writeResult "defenderon_$Dataset" ([ordered]@{ Type = "defenderon"; Dataset = $Dataset; WorkFolderExcludedAfter = $stillCovered; RemovedExclusions = $removed.ToArray(); RemoveMessages = $removeMessages.ToArray(); Before = $before; SetMessage = $message; After = $after })
}

# ---------------------------------------------------------------- share（地図で開いている間に、ファイルを入れ替える・消せるか）

function tryShareAction {
    param ([string]$name, [scriptblock]$action)
    $timer = [System.Diagnostics.Stopwatch]::StartNew()
    $message = ""
    $succeeded = $true
    try { & $action } catch { $succeeded = $false; $message = $_.Exception.Message }
    return [ordered]@{ Name = $name; Succeeded = $succeeded; Ms = [Math]::Round($timer.Elapsed.TotalMilliseconds, 1); Error = $message }
}

function openMapped {
    param ([string]$path, [bool]$withMap, $share)
    $handle = @{ Stream = [System.IO.FileStream]::new($path, [System.IO.FileMode]::Open, [System.IO.FileAccess]::Read, $share); Mapping = $null; View = $null }
    if ($withMap) {
        $handle.Mapping = [System.IO.MemoryMappedFiles.MemoryMappedFile]::CreateFromFile($handle.Stream, [NullString]::Value, 0, [System.IO.MemoryMappedFiles.MemoryMappedFileAccess]::Read, [System.IO.HandleInheritability]::None, $true)
        $handle.View = $handle.Mapping.CreateViewAccessor(0, 0, [System.IO.MemoryMappedFiles.MemoryMappedFileAccess]::Read)
    }
    return $handle
}

function closeMapped {
    param ($handle)
    if ($null -ne $handle.View) { $handle.View.Dispose() }
    if ($null -ne $handle.Mapping) { $handle.Mapping.Dispose() }
    $handle.Stream.Dispose()
}

function newProbeFile {
    param ([string]$path)
    $bytes = New-Object byte[] (8MB)
    [System.IO.File]::WriteAllBytes($path, $bytes)
}

function invokeShare {
    $probeFolder = Join-Path $Work "share_probe"
    [void][System.IO.Directory]::CreateDirectory($probeFolder)
    $shareAll = [System.IO.FileShare]::ReadWrite -bor [System.IO.FileShare]::Delete
    $probes = New-Object System.Collections.ArrayList

    # (a) 8MB の試験ファイルで、開き方ごとの成否を見る
    $cases = @(
        @{ Name = "map_open_delete"; Map = $true; Share = $shareAll; Kind = "delete" },
        @{ Name = "map_open_move"; Map = $true; Share = $shareAll; Kind = "move" },
        @{ Name = "map_open_replace"; Map = $true; Share = $shareAll; Kind = "replace" },
        @{ Name = "stream_only_delete"; Map = $false; Share = $shareAll; Kind = "delete" },
        @{ Name = "stream_only_replace"; Map = $false; Share = $shareAll; Kind = "replace" },
        @{ Name = "map_share_read_delete"; Map = $true; Share = [System.IO.FileShare]::Read; Kind = "delete" },
        @{ Name = "map_share_readwrite_delete"; Map = $true; Share = [System.IO.FileShare]::ReadWrite; Kind = "delete" }
    )
    foreach ($case in $cases) {
        $path = Join-Path $probeFolder ($case.Name + ".bin")
        $other = Join-Path $probeFolder ($case.Name + "_new.bin")
        newProbeFile $path
        if ($case.Kind -eq "replace") { newProbeFile $other }
        $handle = openMapped $path $case.Map $case.Share
        try {
            $kind = $case.Kind
            $moved = Join-Path $probeFolder ($case.Name + "_moved.bin")
            $row = tryShareAction $case.Name {
                if ($kind -eq "delete") { [System.IO.File]::Delete($path) }
                elseif ($kind -eq "move") { [System.IO.File]::Move($path, $moved) }
                else { [void][System.IO.File]::Replace($other, $path, [NullString]::Value) }
            }
            $readable = $true
            try {
                if ($null -ne $handle.View) { [void]$handle.View.ReadByte(0) } else { [void]$handle.Stream.Seek(0, [System.IO.SeekOrigin]::Begin); [void]$handle.Stream.ReadByte() }
            } catch { $readable = $false }
            $row["ReadableAfter"] = $readable
            [void]$probes.Add($row)
        } finally { closeMapped $handle }
    }
    # 開いていないファイル（目次の入れ替え）と、閉じた後の削除
    $indexPath = Join-Path $probeFolder "manifest.txt"
    $indexNew = Join-Path $probeFolder "manifest.new"
    [System.IO.File]::WriteAllText($indexPath, "gen1", $utf8NoBom)
    [System.IO.File]::WriteAllText($indexNew, "gen2", $utf8NoBom)
    [void]$probes.Add((tryShareAction "manifest_replace" { [void][System.IO.File]::Replace($indexNew, $indexPath, [NullString]::Value) }))
    $closedPath = Join-Path $probeFolder "closed.bin"
    newProbeFile $closedPath
    $closedHandle = openMapped $closedPath $true $shareAll
    closeMapped $closedHandle
    [void]$probes.Add((tryShareAction "delete_after_close" { [System.IO.File]::Delete($closedPath) }))

    # (b) 実際の区画を地図で開いたまま、次の世代を書いて目次を替え、古い世代を消す
    $genFolder = Join-Path $Work "share_gen1"
    $nextFolder = Join-Path $Work "share_gen2"
    $sourceFolder = Join-Path $Work "seg_base"
    $names = @("dict.bin", "offs.bin", "lists.bin")
    $flow = New-Object System.Collections.ArrayList
    if ([System.IO.Directory]::Exists($sourceFolder)) {
        [void][System.IO.Directory]::CreateDirectory($genFolder)
        foreach ($name in $names) { [System.IO.File]::Copy((Join-Path $sourceFolder $name), (Join-Path $genFolder $name), $true) }
        $handles = @{}
        foreach ($name in $names) { $handles[$name] = openMapped (Join-Path $genFolder $name) $true $shareAll }
        try {
            # 次の世代を書く（1 ファイルの区画と同じ大きさを、開いたまま書く）
            $nextSource = Join-Path $Work "seg_1"
            if (![System.IO.Directory]::Exists($nextSource)) { $nextSource = $sourceFolder }
            [void]$flow.Add((tryShareAction "write_next_generation" {
                        [void][System.IO.Directory]::CreateDirectory($nextFolder)
                        foreach ($name in $names) { [System.IO.File]::Copy((Join-Path $nextSource $name), (Join-Path $nextFolder $name), $true) }
                    }))
            $manifest = Join-Path $Work "share_manifest.txt"
            $manifestNew = Join-Path $Work "share_manifest.new"
            [System.IO.File]::WriteAllText($manifest, "gen1", $utf8NoBom)
            [System.IO.File]::WriteAllText($manifestNew, "gen2", $utf8NoBom)
            [void]$flow.Add((tryShareAction "swap_manifest" { [void][System.IO.File]::Replace($manifestNew, $manifest, [NullString]::Value) }))
            # 古い世代を、開いたまま消す
            foreach ($name in $names) {
                $target = Join-Path $genFolder $name
                [void]$flow.Add((tryShareAction "delete_old_$name" { [System.IO.File]::Delete($target) }))
            }
            [void]$flow.Add((tryShareAction "delete_old_folder" { [System.IO.Directory]::Delete($genFolder) }))
            $stillReadable = $true
            try { [void]$handles["dict.bin"].View.ReadUInt32(0) } catch { $stillReadable = $false }
            # 開いたまま Directory.Delete が通ると、フォルダはもう無い（一覧する前に有無を見る。無いときは -1）
            $remainWhileOpen = if ([System.IO.Directory]::Exists($genFolder)) { @([System.IO.Directory]::GetFileSystemEntries($genFolder)).Count } else { -1 }
        } finally { foreach ($name in $names) { closeMapped $handles[$name] } }
        $remainAfterClose = if ([System.IO.Directory]::Exists($genFolder)) { @([System.IO.Directory]::GetFileSystemEntries($genFolder)).Count } else { 0 }
        $folderStillThere = [System.IO.Directory]::Exists($genFolder)
        if ($folderStillThere) { [void]$flow.Add((tryShareAction "delete_old_folder_after_close" { [System.IO.Directory]::Delete($genFolder) })) }
        $flowSummary = [ordered]@{ ReadableAfterDelete = $stillReadable; EntriesWhileOpen = $remainWhileOpen; EntriesAfterClose = $remainAfterClose; FolderThereAfterClose = $folderStillThere }
    } else { $flowSummary = [ordered]@{ Error = "seg_base が無い" } }
    # 削除の動き（開いたままでも名前が消えるか）は OS とファイルシステムに依るので、記録する
    $fileSystem = ""
    try { $fileSystem = [System.IO.DriveInfo]::new([System.IO.Path]::GetPathRoot([System.IO.Path]::GetFullPath($Work))).DriveFormat } catch { $fileSystem = "不明: " + $_.Exception.Message }
    $environment = [ordered]@{ OSVersion = [Environment]::OSVersion.VersionString; FileSystem = $fileSystem }
    writeResult "share_$Dataset" ([ordered]@{ Type = "share"; Dataset = $Dataset; Environment = $environment; Probes = $probes.ToArray(); Flow = $flow.ToArray(); FlowSummary = $flowSummary })
}

# ---------------------------------------------------------------- summary

function formatNumber {
    param ($value)
    if ($null -eq $value) { return "" }
    return ([double]$value).ToString("#,##0.##", $culture)
}

function invokeSummary {
    $lines = New-Object System.Collections.ArrayList
    foreach ($path in ([System.IO.Directory]::GetFiles($Out, "*.json") | Sort-Object)) {
        $result = ConvertFrom-Json ([System.IO.File]::ReadAllText($path, $utf8NoBom))
        if ($result.Dataset -ne $Dataset) { continue }
        $name = [System.IO.Path]::GetFileNameWithoutExtension($path)
        switch ($result.Type) {
            "prep" {
                [void]$lines.Add("### データ ($Dataset)")
                [void]$lines.Add("")
                [void]$lines.Add(("- ファイル {0}、合計 {1} 文字、ブロック {2}（{3} 文字ごと）。gram の集合を求める時間 {4} 秒（4 スレッド）、最大メモリ {5} MB" -f $result.Files, (formatNumber $result.TotalChars), $result.Blocks, $result.BlockChars, $result.GramSeconds, $result.PeakMegabytes))
                [void]$lines.Add(("- ファイルごとの異なる gram の数: 最小 {0} / 中央 {1} / 90% {2} / 最大 {3}" -f (formatNumber $result.FileDistinct.Min), (formatNumber $result.FileDistinct.Median), (formatNumber $result.FileDistinct.P90), (formatNumber $result.FileDistinct.Max)))
                [void]$lines.Add(("- ブロックごとの異なる gram の数: 最小 {0} / 中央 {1} / 90% {2} / 最大 {3}" -f (formatNumber $result.BlockDistinct.Min), (formatNumber $result.BlockDistinct.Median), (formatNumber $result.BlockDistinct.P90), (formatNumber $result.BlockDistinct.Max)))
                [void]$lines.Add("")
            }
            "build" {
                [void]$lines.Add(("#### 作成: {0} / {1}単位" -f $result.Shape, $result.Unit))
                [void]$lines.Add("")
                [void]$lines.Add(("- 単位 {0}、異なる gram {1}、行 {2}（重いgram {3}）、分割 {4}" -f $result.Units, (formatNumber $result.Grams), (formatNumber $result.Rows), (formatNumber $result.HeavyGrams), $result.Parts))
                [void]$lines.Add(("- 大きさ {0} MB（{1}）" -f (formatNumber ($result.TotalBytes / 1MB)), (($result.Sizes.PSObject.Properties | ForEach-Object { "{0}={1}MB" -f $_.Name, (formatNumber ($_.Value / 1MB)) }) -join "、")))
                [void]$lines.Add(("- 時間 {0} 秒（読み込み {1}・辞書 {2}・集める {3}・並べ替え {4}・まとめる {5}・形にする {6}・書く {7}）、最大メモリ {8} MB" -f $result.TotalSeconds, $result.LoadSeconds, $result.DictSeconds, $result.GatherSeconds, $result.SortSeconds, $result.GroupSeconds, $result.ShapeSeconds, $result.WriteSeconds, $result.PeakMegabytes))
                if ($null -ne $result.ManagedMegabytesAfterLoad) { [void]$lines.Add(("- 途中のメモリ MB（管理側／最大）: 読み込み後 {0}／{1}、辞書の後 {2}／{3}" -f $result.ManagedMegabytesAfterLoad, $result.PeakMegabytesAfterLoad, $result.ManagedMegabytesAfterDictionary, $result.PeakMegabytesAfterDictionary)) }
                [void]$lines.Add(("- gram が出るファイル数の分布: " + (($result.Histogram.PSObject.Properties | ForEach-Object { "{0}={1}" -f $_.Name, (formatNumber $_.Value) }) -join "、")))
                [void]$lines.Add("")
            }
            { $_ -in @("search", "segsearch") } {
                [void]$lines.Add(("#### 検索: {0}" -f $name))
                [void]$lines.Add("")
                if ($result.Type -eq "segsearch") {
                    [void]$lines.Add(("区画 {0} 個。候補が食い違った語: {1}" -f $result.Segments, $result.DifferentCandidates))
                    if ($null -ne $result.RewriteCheck) { [void]$lines.Add(("書き直しの確かめ: " + ($result.RewriteCheck | ConvertTo-Json -Compress -Depth 4))) }
                    [void]$lines.Add("")
                }
                [void]$lines.Add("| 方法 | 種類 | 語数 | 候補ファイル(中央) | 真のファイル(中央) | 漏れ | 中央値 ms(語の中央) | 最大 ms | 最初の1回 ms(最大) |")
                [void]$lines.Add("|---|---|---|---|---|---|---|---|---|")
                foreach ($method in $result.Methods.PSObject.Properties) {
                    foreach ($kind in $method.Value.ByKind.PSObject.Properties) {
                        $k = $kind.Value
                        [void]$lines.Add(("| {0} | {1} | {2} | {3} | {4} | {5} | {6} | {7} | {8} |" -f $method.Name, $kind.Name, $k.Queries, (formatNumber $k.Files.Median), (formatNumber $k.TrueFiles.Median), $k.Missing, (formatNumber $k.MedianMs.Median), (formatNumber $k.MedianMs.Max), (formatNumber $k.FirstMs.Max)))
                    }
                }
                [void]$lines.Add("")
            }
            "segbuild" {
                [void]$lines.Add("#### 区画の追加")
                [void]$lines.Add("")
                [void]$lines.Add(("- 土台（{0} 単位）{1} 秒。1 ファイルの区画 中央 {2} 秒（最大 {3}）。1 ブック分（{4} gram）の区画 {5} 秒。最大メモリ {6} MB" -f ($result.Units - $result.SegmentUnits), $result.BaseSeconds, $result.OneFileSegmentSeconds.Median, $result.OneFileSegmentSeconds.Max, (formatNumber $result.OneBookGrams), $result.OneBookSegmentSeconds, $result.PeakMegabytes))
                if ($null -ne $result.RewriteSegmentSeconds) { [void]$lines.Add(("- 書き直しの区画（{0} gram）{1} 秒" -f (formatNumber $result.RewriteGrams), $result.RewriteSegmentSeconds)) }
                [void]$lines.Add("")
            }
            "merge" {
                [void]$lines.Add(("#### まとめ直し（区画 {0} 個）" -f $result.Segments))
                [void]$lines.Add("")
                [void]$lines.Add(("- 合計 {0} 秒（区画の読み込み {1}・集める {2}・並べ替え {3}・まとめる {4}・書く {5}）、最大メモリ {6} MB、結果 {7} MB" -f $result.TotalSeconds, $result.LoadSeconds, $result.GatherSeconds, $result.SortSeconds, $result.GroupSeconds, $result.WriteSeconds, $result.PeakMegabytes, (formatNumber ($result.TotalBytes / 1MB))))
                [void]$lines.Add("")
            }
            "defenderon" {
                [void]$lines.Add("#### Defender のリアルタイム保護を有効にする試み")
                [void]$lines.Add("")
                if ($null -ne $result.Skipped) { [void]$lines.Add("- " + $result.Skipped) } else {
                    [void]$lines.Add(("- 前: " + ($result.Before | ConvertTo-Json -Compress)))
                    [void]$lines.Add(("- 設定したときのメッセージ: " + $result.SetMessage))
                    [void]$lines.Add(("- 外した除外: " + (@($result.RemovedExclusions) -join "、") + "（外せなかった: " + (@($result.RemoveMessages) -join "、") + "）"))
                    [void]$lines.Add(("- 作業フォルダが除外に含まれたまま: {0}" -f $result.WorkFolderExcludedAfter))
                    [void]$lines.Add(("- 後: " + ($result.After | ConvertTo-Json -Compress)))
                }
                [void]$lines.Add("")
            }
            "share" {
                [void]$lines.Add("#### 地図で開いている間の削除・移動・入れ替え")
                [void]$lines.Add("")
                [void]$lines.Add("| 試し | 成否 | ms | 開いたままの読み出し | 例外 |")
                [void]$lines.Add("|---|---|---|---|---|")
                foreach ($probe in $result.Probes) {
                    [void]$lines.Add(("| {0} | {1} | {2} | {3} | {4} |" -f $probe.Name, $probe.Succeeded, $probe.Ms, $probe.ReadableAfter, $probe.Error))
                }
                [void]$lines.Add("")
                [void]$lines.Add("| 世代の入れ替え | 成否 | ms | 例外 |")
                [void]$lines.Add("|---|---|---|---|")
                foreach ($step in $result.Flow) {
                    [void]$lines.Add(("| {0} | {1} | {2} | {3} |" -f $step.Name, $step.Succeeded, $step.Ms, $step.Error))
                }
                [void]$lines.Add("")
                [void]$lines.Add(("- 環境: " + ($result.Environment | ConvertTo-Json -Compress)))
                [void]$lines.Add(("- " + ($result.FlowSummary | ConvertTo-Json -Compress)))
                [void]$lines.Add("")
            }
            "defender" {
                [void]$lines.Add("#### 初めて開く時間（Defender）")
                [void]$lines.Add("")
                [void]$lines.Add(("- Defender: " + ($result.Status | ConvertTo-Json -Compress)))
                [void]$lines.Add("")
                [void]$lines.Add("| ファイル | MB | 書く ms | 初めて開く ms | 初めて全部読む ms | 続けて開く ms | 続けてもう一度読む ms |")
                [void]$lines.Add("|---|---|---|---|---|---|---|")
                foreach ($file in $result.Files) {
                    [void]$lines.Add(("| {0} | {1} | {2} | {3} | {4} | {5} | {6} |" -f $file.Name, (formatNumber $file.Megabytes), (formatNumber $file.WriteMs), $file.First.FirstOpenMs, $file.First.FirstReadAllMs, $file.First.SecondOpenMs, $file.First.SecondReadAllMs))
                }
                [void]$lines.Add("")
            }
        }
    }
    $text = ($lines -join "`n")
    [System.IO.File]::WriteAllText((Join-Path $Out "summary_$Dataset.md"), $text, $utf8NoBom)
    Write-Host $text
    if ($env:GITHUB_STEP_SUMMARY) { [System.IO.File]::AppendAllText($env:GITHUB_STEP_SUMMARY, $text + "`n", $utf8NoBom) }
}

switch ($Stage) {
    "prep" { invokePrep }
    "build" { invokeBuild }
    "search" { invokeSearch }
    "segbuild" { invokeSegmentBuild }
    "merge" { invokeMerge }
    "segsearch" { invokeSegmentSearch }
    "defenderon" { invokeDefenderOn }
    "share" { invokeShare }
    "defender" { invokeDefender }
    "summary" { invokeSummary }
}
