$patterns = @('VKOSPI','KVI200','KVI','VIX','공포','변동')
$files = Get-ChildItem 'D:\25server\project\chunk_*.js'
foreach($file in $files){
  $text = Get-Content $file.FullName -Raw
  foreach($p in $patterns){
    $idx = $text.IndexOf($p, [System.StringComparison]::OrdinalIgnoreCase)
    if($idx -ge 0){
      $start = [Math]::Max(0, $idx - 120)
      $len = [Math]::Min(320, $text.Length - $start)
      $ctx = $text.Substring($start, $len)
      Write-Output "FOUND $p in $($file.Name) at $idx"
      Write-Output $ctx
      Write-Output '----'
      break
    }
  }
}
