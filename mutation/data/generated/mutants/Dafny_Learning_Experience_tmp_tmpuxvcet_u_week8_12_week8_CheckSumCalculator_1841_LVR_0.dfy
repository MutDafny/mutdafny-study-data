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
  var newSeq := ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'];
  var newSeqTwo := ['h', 'g', 'f', 'e', 'd', 'c', 'b', 'a'];
  var newSet: set<int>;
  newSet := {0, 2, 3, 4, 5};
  var newSetTwo := {6, 7, 8, 9, 10};
  print "element is newset ", newSet, "\n";
  var newArray := new int[99];
  newArray[0] := 99;
  newArray[1] := 2;
  print "element is ?  ", |[newArray]|, "\n";
  var tmpSet := {'a', 'c'};
  var tmpFresh := {'c'};
  print "tmp is ", tmpSet - tmpFresh;
  var newMap := map[];
  newMap := newMap[1 := 2];
  var nnewMap := map[3 := 444];
  print "keys is ", newMap.Keys, newMap.Values;
  print "value is", nnewMap.Keys, nnewMap.Values;
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
