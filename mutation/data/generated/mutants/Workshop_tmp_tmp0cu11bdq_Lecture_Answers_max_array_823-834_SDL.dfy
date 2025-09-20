// Workshop_tmp_tmp0cu11bdq_Lecture_Answers_max_array.dfy

method max(a: array<int>) returns (max: int)
  requires a != null
  ensures forall j: int {:trigger a[j]} :: j >= 0 && j < a.Length ==> max >= a[j]
  ensures a.Length > 0 ==> exists j: int {:trigger a[j]} :: j >= 0 && j < a.Length && max == a[j]
  decreases a
{
  if a.Length == 0 {
    max := 0;
    return;
  }
  max := a[0];
  var i := 1;
  while i < a.Length
    invariant i <= a.Length
    invariant forall j: int {:trigger a[j]} :: 0 <= j < i ==> max >= a[j]
    invariant exists j: int {:trigger a[j]} :: 0 <= j < i && max == a[j]
    decreases a.Length - i
  {
    if a[i] > max {
    }
    i := i + 1;
  }
}
