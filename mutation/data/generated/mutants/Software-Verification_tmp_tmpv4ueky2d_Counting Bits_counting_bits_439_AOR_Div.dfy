// Software-Verification_tmp_tmpv4ueky2d_Counting Bits_counting_bits.dfy

method counting_bits(n: int) returns (result: array<int>)
  requires 0 <= n <= 100000
  ensures result.Length == n + 1
  ensures forall i: int {:trigger i % 2} {:trigger i / 2} :: 1 <= i < n + 1 ==> result[i] == result[i / 2] + i % 2
  decreases n
{
  result := new int[n + 1] ((i: nat) => 0);
  var i := 1;
  while i < n + 1
    invariant 1 <= i <= n + 1
    invariant forall j: int {:trigger j % 2} {:trigger j / 2} :: 1 <= j < i ==> result[j] == result[j / 2] + j % 2
    decreases n + 1 - i
  {
    result[i] := result[i / 2] + i / 2;
    i := i + 1;
  }
}
