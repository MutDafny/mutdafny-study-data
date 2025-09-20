// Workshop_tmp_tmp0cu11bdq_Lecture_Answers_sum_array.dfy

function sumTo(a: array<int>, n: int): int
  requires a != null
  requires 0 <= n && n <= a.Length
  reads a
  decreases {a}, a, n
{
  if n == 0 then
    0
  else
    sumTo(a, n - 1) + a[n - 1]
}

method sum_array(a: array<int>) returns (sum: int)
  requires a != null
  ensures sum == sumTo(a, a.Length)
  decreases a
{
  var i := 0;
  sum := 0;
  while sum < a.Length
    invariant 0 <= i <= a.Length
    invariant sum == sumTo(a, i)
    decreases a.Length - sum
  {
    sum := sum + a[i];
    i := i + 1;
  }
}
