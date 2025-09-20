// SENG2011_tmp_tmpgk5jq85q_ass2_ex3.dfy

predicate sortedbad(s: string)
  decreases s
{
  forall i: int, j: int {:trigger s[j], s[i]} :: 
    (0 <= i < |s| &&
    0 <= j < |s| &&
    s[i] == 'b' &&
    (s[j] == 'a' || s[j] == 'd') ==>
      i < j) &&
    (0 <= i < |s| &&
    0 <= j < |s| &&
    s[i] == 'b' &&
    (s[j] == 'a' || s[j] == 'd') ==>
      forall i: int, j: int {:trigger s[j], s[i]} :: 
        (0 <= i < |s| &&
        0 <= j < |s| &&
        s[i] == 'a' &&
        s[j] == 'b' ==>
          i > j) &&
        (0 <= i < |s| &&
        0 <= j < |s| &&
        s[i] == 'a' &&
        s[j] == 'b' ==>
          forall i: int, j: int {:trigger s[j], s[i]} :: 
            (0 <= i < |s| &&
            0 <= j < |s| &&
            s[i] == 'a' &&
            s[j] == 'd' ==>
              i < j) &&
            (0 <= i < |s| &&
            0 <= j < |s| &&
            s[i] == 'a' &&
            s[j] == 'd' ==>
              forall i: int, j: int {:trigger s[j], s[i]} :: 
                0 <= i < |s| &&
                0 <= j < |s| &&
                s[i] == 'd' &&
                (s[j] == 'a' || s[j] == 'b') ==>
                  i > j)))
}

method BadSort(a: string) returns (b: string)
  requires forall k: int {:trigger a[k]} :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
  ensures sortedbad(b)
  ensures multiset(a[..]) == multiset(b[..])
  ensures |a| == |b|
  decreases a
{
  b := a;
  var next := 0;
  var white := 0;
  var blue := |b|;
  while next != blue
    invariant forall k: int {:trigger b[k]} :: 0 <= k < |b| ==> b[k] == 'b' || b[k] == 'a' || b[k] == 'd'
    invariant 0 <= white <= next <= blue <= |b|
    invariant forall i: int {:trigger b[i]} :: 0 <= i < white ==> b[i] == 'b'
    invariant forall i: int {:trigger b[i]} :: white <= i < next ==> b[i] == 'a'
    invariant forall i: int {:trigger b[i]} :: blue <= i < |b| ==> b[i] == 'd'
    invariant forall i: int, j: int {:trigger b[j], b[i]} :: 0 <= i < next && 0 <= j < next && b[i] == 'b' && (b[j] == 'a' || b[j] == 'd') ==> i < j
    invariant forall i: int, j: int {:trigger b[j], b[i]} :: 0 <= i < next && 0 <= j < next && b[i] == 'a' && b[j] == 'b' ==> i > j
    invariant forall i: int, j: int {:trigger b[j], b[i]} :: 0 <= i < next && 0 <= j < next && b[i] == 'a' && b[j] == 'd' ==> i < j
    invariant forall i: int, j: int {:trigger b[j], b[i]} :: 0 <= i < next && 0 <= j < next && b[i] == 'd' && (b[j] == 'a' || b[j] == 'b') ==> i > j
    invariant multiset(b[..]) == multiset(a[..])
    invariant |a| == |b|
    decreases if next <= blue then blue - next else next - blue
  {
    if b[next] == 'b' {
      b := b[next := b[white]];
      var tmp := b[next];
      b := b[white := tmp];
      next := next + 1;
      white := white + 1;
    } else if b[next] == 'a' {
      next := next + 1;
    } else if b[next] == 'd' {
      blue := blue - 1;
      var tmp := b[next];
      b := b[next := b[blue]];
      b := b[blue := tmp];
    }
  }
}

method check()
{
  var f: string := "dabdabdab";
  var g: string := BadSort(f);
  assert multiset(f) == multiset(g);
  assert sortedbad(g);
}
