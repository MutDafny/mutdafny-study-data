// dafny_tmp_tmp59p638nn_examples_minmax2.dfy

method DifferenceMinMax(a: array<int>) returns (diff: int)
  requires a.Length > 0
  ensures diff == Max(a[..]) - Min(a[..])
  decreases a
{
  var minVal := a[0];
  var maxVal := a[0];
  for i: int := 1 to a.Length
    invariant 1 <= i <= a.Length
    invariant minVal <= maxVal
    invariant forall k: int {:trigger a[k]} :: (0 <= k < i ==> minVal <= a[k]) && (0 <= k < i ==> a[k] <= maxVal)
    invariant minVal == Min(a[..i])
    invariant maxVal == Max(a[..i])
  {
    maxVal := a[i];
    assert a[..i + 1][..i] == a[..i];
  }
  assert a[..a.Length] == a[..];
  diff := maxVal - minVal;
}

function Min(a: seq<int>): (m: int)
  requires |a| > 0
  decreases a
{
  if |a| == 1 then
    a[0]
  else
    var minPrefix: int := Min(a[..|a| - 1]); if a[|a| - 1] <= minPrefix then a[|a| - 1] else minPrefix
}

function Max(a: seq<int>): (m: int)
  requires |a| > 0
  decreases a
{
  if |a| == 1 then
    a[0]
  else
    var maxPrefix: int := Max(a[..|a| - 1]); if a[|a| - 1] >= maxPrefix then a[|a| - 1] else maxPrefix
}
