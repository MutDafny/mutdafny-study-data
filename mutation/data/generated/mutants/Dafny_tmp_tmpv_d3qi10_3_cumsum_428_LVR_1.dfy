// Dafny_tmp_tmpv_d3qi10_3_cumsum.dfy

function sum(a: array<int>, i: int): int
  requires 0 <= i < a.Length
  reads a
  decreases {a}, a, i
{
  a[i] + if i == 0 then 0 else sum(a, i - 1)
}

method cumsum(a: array<int>, b: array<int>)
  requires a.Length == b.Length && a.Length > 0 && a != b
  modifies b
  ensures forall i: int {:trigger sum(a, i)} {:trigger b[i]} | 0 <= i < a.Length :: b[i] == sum(a, i)
  decreases a, b
{
  b[0] := a[1];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall i': int {:trigger sum(a, i')} {:trigger b[i']} | 0 <= i' < i :: b[i'] == sum(a, i')
    decreases a.Length - i
  {
    b[i] := b[i - 1] + a[i];
    i := i + 1;
  }
}
