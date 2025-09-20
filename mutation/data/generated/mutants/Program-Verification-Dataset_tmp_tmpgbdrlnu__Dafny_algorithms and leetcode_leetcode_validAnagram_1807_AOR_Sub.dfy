// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_leetcode_validAnagram.dfy

method toMultiset(s: string) returns (mset: multiset<char>)
  ensures multiset(s) == mset
  decreases s
{
  mset := multiset{};
  for i: int := 0 to |s|
    invariant mset == multiset(s[0 .. i])
  {
    assert s == s[0 .. i] + [s[i]] + s[i + 1..];
    mset := mset + multiset{s[i]};
  }
  assert s == s[0 .. |s|];
  return mset;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
  ensures s == t <==> equal
  decreases s, t
{
  ghost var sremoved: multiset<char> := multiset{};
  var scopy := s;
  while scopy != multiset{}
    invariant s - sremoved == scopy
    invariant sremoved !! scopy
    invariant sremoved <= s
    invariant forall x: char {:trigger t[x]} {:trigger s[x]} {:trigger sremoved[x]} :: (x in sremoved ==> x in s) && (x in sremoved ==> x in t) && (x in sremoved ==> t[x] == s[x])
    decreases scopy
  {
    var x :| x in scopy;
    if !(x in t && s[x] == t[x]) {
      return false;
    }
    var removed := multiset{};
    sremoved := sremoved + removed[x := s[x]];
    scopy := scopy - removed[x := s[x]];
  }
  ghost var tremoved: multiset<char> := multiset{};
  var tcopy := t;
  while tcopy != multiset{}
    invariant t - tremoved == tcopy
    invariant tremoved !! tcopy
    invariant tremoved <= t
    invariant forall x: char {:trigger t[x]} {:trigger s[x]} {:trigger tremoved[x]} :: (x in tremoved ==> x in s) && (x in tremoved ==> x in t) && (x in tremoved ==> t[x] == s[x])
    decreases tcopy
  {
    var x :| x in tcopy;
    if !(x in t && s[x] == t[x]) {
      return false;
    }
    var removed := multiset{};
    tremoved := tremoved - removed[x := s[x]];
    tcopy := tcopy - removed[x := s[x]];
  }
  return true;
}

method isAnagram(s: string, t: string) returns (equal: bool)
  ensures (multiset(s) == multiset(t)) == equal
  decreases s, t
{
  var smset := toMultiset(s);
  var tmset := toMultiset(t);
  equal := msetEqual(smset, tmset);
}
