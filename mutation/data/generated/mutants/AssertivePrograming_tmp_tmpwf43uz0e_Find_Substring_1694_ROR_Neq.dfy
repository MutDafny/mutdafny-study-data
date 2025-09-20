// AssertivePrograming_tmp_tmpwf43uz0e_Find_Substring.dfy

ghost predicate ExistsSubstring(str1: string, str2: string)
  decreases str1, str2
{
  exists offset: int {:trigger str1[offset..]} :: 
    0 <= offset <= |str1| &&
    str2 <= str1[offset..]
}

ghost predicate Post(str1: string, str2: string, found: bool, i: nat)
  decreases str1, str2, found, i
{
  (found <==> ExistsSubstring(str1, str2)) &&
  (found ==>
    i + |str2| <= |str1| &&
    str2 <= str1[i..])
}

method {:verify true} FindFirstOccurrence(str1: string, str2: string)
    returns (found: bool, i: nat)
  ensures Post(str1, str2, found, i)
  decreases str1, str2
{
  if |str2| == 0 {
    found, i := true, 0;
    assert Post(str1, str2, found, i);
  } else if |str1| < |str2| {
    found, i := false, 0;
    assert Post(str1, str2, found, i);
  } else {
    found, i := false, |str2| - 1;
    assert |str2| > 0;
    assert |str1| >= |str2|;
    assert Outter_Inv_correctness(str1, str2, false, |str2| - 1);
    while !found && i < |str1|
      invariant Outter_Inv_correctness(str1, str2, found, i)
      decreases if !found then 1 else 0, |str1| - i
    {
      assert Outter_Inv_correctness(str1, str2, found, i);
      assert |str2| > 0;
      assert !found && i < |str1|;
      var j := |str2| - 1;
      ghost var old_i := i;
      ghost var old_j := j;
      while !found && str1[i] != str2[j]
        invariant Inner_Inv_Termination(str1, str2, i, j, old_i, old_j)
        invariant Inner_Inv_correctness(str1, str2, i, j, found)
        decreases j, if !found then 1 else 0
      {
        if j == 0 {
          assert j == 0 && str1[i] == str2[j];
          found := true;
          assert Inner_Inv_Termination(str1, str2, i, j, old_i, old_j);
          assert Inner_Inv_correctness(str1, str2, i, j, found);
        } else {
          assert j > 0;
          assert Inner_Inv_Termination(str1, str2, i - 1, j - 1, old_i, old_j);
          assert Inner_Inv_correctness(str1, str2, i - 1, j - 1, found);
          i, j := i - 1, j - 1;
          assert Inner_Inv_Termination(str1, str2, i, j, old_i, old_j);
          assert Inner_Inv_correctness(str1, str2, i, j, found);
        }
        assert j >= 0;
        assert Inner_Inv_Termination(str1, str2, i, j, old_i, old_j);
        assert Inner_Inv_correctness(str1, str2, i, j, found);
      }
      assert Inner_Inv_Termination(str1, str2, i, j, old_i, old_j);
      assert Inner_Inv_correctness(str1, str2, i, j, found);
      assert found || str1[i] != str2[j];
      assert found ==> i + |str2| <= |str1| && str2 <= str1[i..];
      assert !found ==> str1[i] != str2[j];
      if !found {
        assert i < |str1|;
        assert |str2| > 0;
        assert old_j - j == old_i - i;
        assert old_i < i + |str2| - j;
        assert Outter_Inv_correctness(str1, str2, found, old_i);
        assert i + |str2| - j == old_i + 1;
        assert str1[i] != str2[j];
        assert |str1[old_i + 1 - |str2| .. old_i + 1]| == |str2|;
        assert str1[old_i + 1 - |str2| .. old_i + 1] != str2;
        assert 0 < old_i <= |str1| ==> !ExistsSubstring(str1[..old_i], str2);
        Lemma1(str1, str2, i, j, old_i, old_j, found);
        assert 0 < old_i + 1 <= |str1| ==> !ExistsSubstring(str1[..old_i + 1], str2);
        assert 0 < i + |str2| - j <= |str1| ==> !ExistsSubstring(str1[..i + |str2| - j], str2);
        assert Outter_Inv_correctness(str1, str2, found, i + |str2| - j);
        i := i + |str2| - j;
        assert old_i < i;
        assert Outter_Inv_correctness(str1, str2, found, i);
        assert i <= |str1|;
      }
      assert !found ==> i <= |str1|;
      assert !found ==> old_i < i;
      assert !found ==> Outter_Inv_correctness(str1, str2, found, i);
      assert found ==> Outter_Inv_correctness(str1, str2, found, i);
      assert Outter_Inv_correctness(str1, str2, found, i);
    }
    assert Outter_Inv_correctness(str1, str2, found, i);
    assert found ==> i + |str2| <= |str1| && str2 <= str1[i..];
    assert !found && 0 < i <= |str1| ==> !ExistsSubstring(str1[..i], str2);
    assert !found ==> i <= |str1|;
    assert found || i >= |str1|;
    assert !found && i == |str1| ==> !ExistsSubstring(str1[..i], str2);
    assert i == |str1| ==> str1[..i] == str1;
    assert !found && i == |str1| ==> !ExistsSubstring(str1, str2);
    assert !found ==> i >= |str1|;
    assert !found ==> i == |str1|;
    assert !found ==> !ExistsSubstring(str1, str2);
    assert found ==> ExistsSubstring(str1, str2);
    assert found <==> ExistsSubstring(str1, str2);
    assert found ==> i + |str2| <= |str1| && str2 <= str1[i..];
    assert Post(str1, str2, found, i);
  }
  assert Post(str1, str2, found, i);
}

method Main()
{
  var str1a, str1b := "string", " in Dafny is a sequence of characters (seq<char>)";
  var str1, str2 := str1a + str1b, "ring";
  var found, i := FindFirstOccurrence(str1, str2);
  assert found by {
    assert ExistsSubstring(str1, str2) by {
      ghost var offset := 2;
      assert 0 <= offset <= |str1|;
      assert str2 <= str1[offset..] by {
        assert str2 == str1[offset..][..4];
      }
    }
  }
  print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
  if found {
    print " and i == ", i;
  }
  str1 := "<= on sequences is the prefix relation";
  found, i := FindFirstOccurrence(str1, str2);
  print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
  if found {
    print " and i == ", i;
  }
}

ghost predicate Outter_Inv_correctness(str1: string, str2: string, found: bool, i: nat)
  decreases str1, str2, found, i
{
  (found ==>
    i + |str2| <= |str1| &&
    str2 <= str1[i..]) &&
  (!found &&
  0 < i <= |str1| &&
  i != |str2| - 1 ==>
    !ExistsSubstring(str1[..i], str2)) &&
  (!found ==>
    i <= |str1|)
}

ghost predicate Inner_Inv_correctness(str1: string, str2: string, i: nat, j: int, found: bool)
  decreases str1, str2, i, j, found
{
  0 <= j <= i &&
  j < |str2| &&
  i < |str1| &&
  (str1[i] == str2[j] ==>
    str2[j..] <= str1[i..]) &&
  (found ==>
    j == 0 &&
    str1[i] == str2[j])
}

ghost predicate Inner_Inv_Termination(str1: string, str2: string, i: nat, j: int, old_i: nat, old_j: nat)
  decreases str1, str2, i, j, old_i, old_j
{
  old_j - j == old_i - i
}

lemma {:verify true} Lemma1(str1: string, str2: string, i: nat, j: int, old_i: nat, old_j: nat, found: bool)
  requires !found
  requires |str2| > 0
  requires Outter_Inv_correctness(str1, str2, found, old_i)
  requires i + |str2| - j == old_i + 1
  requires old_i + 1 >= |str2|
  requires old_i + 1 <= |str1|
  requires 0 <= i < |str1| && 0 <= j < |str2|
  requires str1[i] != str2[j]
  requires |str2| > 0
  requires 0 < old_i <= |str1| ==> !ExistsSubstring(str1[..old_i], str2)
  ensures 0 < old_i + 1 <= |str1| ==> !ExistsSubstring(str1[..old_i + 1], str2)
  decreases str1, str2, i, j, old_i, old_j, found
{
  assert |str1[old_i + 1 - |str2| .. old_i + 1]| == |str2|;
  assert str1[old_i + 1 - |str2| .. old_i + 1] != str2;
  assert !(str2 <= str1[old_i + 1 - |str2| .. old_i + 1]);
  assert 0 <= old_i < old_i + 1 <= |str1|;
  assert old_i + 1 >= |str2|;
  calc {
    0 < old_i + 1 <= |str1| &&
    ExistsSubstring(str1[..old_i + 1], str2) &&
    !(str2 <= str1[old_i + 1 - |str2| .. old_i + 1]);
  ==>
    !ExistsSubstring(str1[..old_i], str2) &&
    ExistsSubstring(str1[..old_i + 1], str2) &&
    !(str2 <= str1[old_i + 1 - |str2| .. old_i + 1]);
  ==>
    {
      Lemma2(str1, str2, old_i, found);
    }
    (0 < old_i < old_i + 1 <= |str1| &&
    old_i != |str2| - 1 ==>
      |str1[old_i + 1 - |str2| .. old_i + 1]| == |str2| &&
      str2 <= str1[old_i + 1 - |str2| .. old_i + 1]) &&
    !(str2 <= str1[old_i + 1 - |str2| .. old_i + 1]);
  ==>
    0 < old_i < old_i + 1 <= |str1| &&
    old_i != |str2| - 1 ==>
      false;
  }
}

lemma {:verify true} Lemma2(str1: string, str2: string, i: nat, found: bool)
  requires 0 <= i < |str1|
  requires 0 < |str2| <= i + 1
  requires !ExistsSubstring(str1[..i], str2)
  requires ExistsSubstring(str1[..i + 1], str2)
  ensures str2 <= str1[i + 1 - |str2| .. i + 1]
  decreases str1, str2, i, found
{
  assert exists offset: int :: (0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && offset <= i) || (0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && offset == i + 1);
  calc {
    0 < |str2| &&
    !(exists offset: int {:trigger str1[offset .. i]} :: 0 <= offset <= i && str2 <= str1[offset .. i]) &&
    exists offset: int :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1];
  ==>
    0 < |str2| &&
    (forall offset: int {:trigger str1[offset .. i]} :: 
      0 <= offset <= i ==>
        !(str2 <= str1[offset .. i])) &&
    exists offset: int :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1];
  ==>
    0 < |str2| &&
    (exists offset: int :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1]) &&
    forall offset: int {:trigger str1[offset .. i]} :: 
      0 <= offset <= i + 1 ==>
        offset <= i ==>
          !(str2 <= str1[offset .. i]);
  ==>
    {
      Lemma3(str1, str2, i);
    }
    0 < |str2| &&
    exists offset: int {:trigger str1[offset .. i]} :: 
      (0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && !(offset <= i)) || (0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && !(str2 <= str1[offset .. i]));
  ==>
    0 < |str2| &&
    exists offset: int {:trigger str1[offset .. i]} :: 
      (0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && (offset <= i ==> !(str2 <= str1[offset .. i])) && !(offset == i + 1)) || (0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && (offset <= i ==> !(str2 <= str1[offset .. i])) && |str2| == 0);
  ==>
    0 < |str2| &&
    exists offset: int {:trigger str1[offset .. i]} :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1] &&
      (offset <= i ==>
        !(str2 <= str1[offset .. i])) &&
      (offset == i + 1 ==>
        |str2| == 0) &&
      offset != i + 1;
  ==>
    0 < |str2| &&
    exists offset: int {:trigger str1[offset .. i]} :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1] &&
      (offset <= i ==>
        !(str2 <= str1[offset .. i])) &&
      offset <= i;
  ==>
    0 < |str2| &&
    exists offset: int {:trigger str1[offset .. i]} :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1] &&
      !(str2 <= str1[offset .. i]);
  ==>
    str2 <= str1[i + 1 - |str2| .. i + 1];
  }
}

lemma Lemma3(str1: string, str2: string, i: nat)
  requires 0 <= i < |str1|
  requires 0 < |str2| <= i + 1
  requires exists offset: int :: 0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1]
  requires forall offset: int {:trigger str1[offset .. i]} :: 0 <= offset <= i + 1 ==> offset <= i ==> !(str2 <= str1[offset .. i])
  ensures exists offset: int {:trigger str1[offset .. i]} :: (0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && !(offset <= i)) || (0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && !(str2 <= str1[offset .. i]))
  decreases str1, str2, i
{
  ghost var offset :| 0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1];
  assert 0 <= offset <= i + 1 ==> offset <= i ==> !(str2 <= str1[offset .. i]);
}
