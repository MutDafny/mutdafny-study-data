// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_Test_c++_arrays.dfy

method returnANullArray() returns (a: array?<uint32>)
  ensures a == null
{
  a := null;
}

method returnANonNullArray() returns (a: array?<uint32>)
  ensures a != null
  ensures a.Length == 5
{
  a := new uint32[5];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 4;
  a[4] := 5;
}

method LinearSearch(a: array<uint32>, len: uint32, key: uint32)
    returns (n: uint32)
  requires a.Length == len as int
  ensures 0 <= n <= len
  ensures n == len || a[n] == key
  decreases a, len, key
{
  n := 0;
  while n < len
    invariant n <= len
    decreases len as int - n as int
  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
}

method PrintArray<A>(a: array?<A>, len: uint32)
  requires a != null ==> len as int == a.Length
  decreases a, len
{
  if a == null {
    print "It's null\n";
  } else {
    var i: uint32 := 0;
    while i < len
      decreases len as int - i as int
    {
      print a[i], " ";
      i := i + 1;
    }
    print "\n";
  }
}

method Main()
{
}

newtype uint32 = i: int
  | 0 <= i < 4294967296

datatype ArrayDatatype = AD(ar: array<uint32>)
