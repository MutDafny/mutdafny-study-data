// Dafny_Learning_Experience_tmp_tmpuxvcet_u_week8_12_week8_CheckSumCalculator.dfy

ghost function Hash(s: string): int
  decreases s
{
  SumChars(s) % 137
}

ghost function SumChars(s: string): int
  decreases s
{
  if |s| == 0 then
    0
  else
    s[|s| - 1] as int + SumChars(s[..|s| - 1])
}

method Main()
{
}

class CheckSumCalculator {
  var data: string
  var cs: int

  ghost predicate Valid()
    reads this
    decreases {this}
  {
    cs == Hash(data)
  }

  constructor ()
    ensures Valid() && data == ""
  {
    data, cs := "", 0;
  }

  method Append(d: string)
    requires Valid()
    modifies this
    ensures Valid() && data == old(data) + d
    decreases d
  {
    var i := 0;
    while i != |d|
      invariant 0 <= i <= |d|
      invariant Valid()
      invariant data == old(data) + d[..i]
      decreases if i <= |d| then |d| - i else i - |d|
    {
      cs := (cs + d[i] as int) % 137;
      data := data + [d[i]];
      i := i + 1;
    }
  }

  function GetData(): string
    requires Valid()
    reads this
    ensures Hash(GetData()) == Checksum()
    decreases {this}
  {
    data
  }

  function Checksum(): int
    requires Valid()
    reads this
    ensures Checksum() == Hash(data)
    decreases {this}
  {
    cs
  }
}
