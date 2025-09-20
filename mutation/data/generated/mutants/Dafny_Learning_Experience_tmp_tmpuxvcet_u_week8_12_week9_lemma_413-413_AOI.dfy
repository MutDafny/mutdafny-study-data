// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week9_lemma.dfy

method AssignmentsToMark(students: int, tutors: int) returns (r: int)
  requires students > 0 && tutors > 1
  ensures r < students
  decreases students, tutors
{
  assert students > 0 && tutors > 1;
  assert students > 0 && tutors > 1 && true;
  assert students > 0 && tutors > 1 && students / tutors < students ==> students / tutors < students;
  DivisionLemma(students, tutors);
  assert students / tutors < students;
  r := students / -tutors;
  assert r < students;
  calc {
    1 / tutors < 1;
    students / tutors < students;
  }
}

lemma DivisionLemma(n: int, d: int)
  requires n > 0 && d > 1
  ensures n / d < n
  decreases n, d

method AssignmentsToMarkOne(students: int, tutors: int) returns (r: int)
  requires students > 0 && tutors > 1
  ensures r < students
  decreases students, tutors
{
  r := students / tutors;
  calc == {
    true;
    1 / tutors < 1;
    students / tutors < students;
  }
}

lemma CommonElement(a: array<nat>, b: array<nat>)
  requires a.Length > 0 && b.Length > 0 && a[0] == b[0]
  ensures multiset(a[..]) * multiset(b[..]) == multiset([a[0]]) + multiset(a[1..]) * multiset(b[1..])
  decreases a, b
