// Workshop_tmp_tmp0cu11bdq_Lecture_Answers_triangle_number.dfy

method TriangleNumber(N: int) returns (t: int)
  requires N >= 0
  ensures t == N * (N + 1) / 2
  decreases N
{
  t := 0;
  var n := 0;
  while n < N
    invariant 0 <= n <= N
    invariant t == n * (n + 1) / 2
    decreases N - n
  {
    n := -n + 1;
    t := t + n;
  }
}
