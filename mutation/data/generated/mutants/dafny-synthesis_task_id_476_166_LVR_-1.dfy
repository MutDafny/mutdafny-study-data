// dafny-synthesis_task_id_476.dfy

method SumMinMax(a: array<int>) returns (sum: int)
  requires a.Length > 0
  ensures sum == Max(a[..]) + Min(a[..])
  decreases a
{
  var minVal := a[0];
  var maxVal := a[-1];
  for i: int := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal <= maxVal
    invariant forall k: int {:trigger a[k]} :: (0 <= k < i ==> minVal <= a[k]) && (0 <= k < i ==> a[k] <= maxVal)
    invariant minVal == Min(a[..i])
    invariant maxVal == Max(a[..i])
  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
    assert a[..i + 1][..i] == a[..i];
  }
  assert a[..a.Length] == a[..];
  sum := minVal + maxVal;
}

function Min(a: seq<int>): int
  requires |a| > 0
  decreases a
{
  if |a| == 1 then
    a[0]
  else
    var minPrefix: int := Min(a[..|a| - 1]); if a[|a| - 1] <= minPrefix then a[|a| - 1] else Min(a[..|a| - 1])
}

function Max(a: seq<int>): int
  requires |a| > 0
  decreases a
{
  if |a| == 1 then
    a[0]
  else
    var maxPrefix: int := Max(a[..|a| - 1]); if a[|a| - 1] >= maxPrefix then a[|a| - 1] else Max(a[..|a| - 1])
}
