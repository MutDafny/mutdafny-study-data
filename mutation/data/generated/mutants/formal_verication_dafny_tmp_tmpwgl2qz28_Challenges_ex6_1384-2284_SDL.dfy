// formal_verication_dafny_tmp_tmpwgl2qz28_Challenges_ex6.dfy

function bullspec(s: seq<nat>, u: seq<nat>): nat
  requires 0 <= |u| == |s| && nomultiples(u)
  decreases s, u
{
  reccbull(s, u, 0)
}

function cowspec(s: seq<nat>, u: seq<nat>): nat
  requires 0 <= |u| == |s| && nomultiples(u)
  decreases s, u
{
  recccow(s, u, 0)
}

function reccbull(s: seq<nat>, u: seq<nat>, i: int): nat
  requires 0 <= i <= |s| == |u|
  decreases |s| - i
{
  if i == |s| then
    0
  else if s[i] == u[i] then
    reccbull(s, u, i + 1) + 1
  else
    reccbull(s, u, i + 1)
}

function recccow(s: seq<nat>, u: seq<nat>, i: int): nat
  requires 0 <= i <= |s| == |u|
  decreases |s| - i
{
  if i == |s| then
    0
  else if s[i] != u[i] && u[i] in s then
    recccow(s, u, i + 1) + 1
  else
    recccow(s, u, i + 1)
}

predicate nomultiples(u: seq<nat>)
  decreases u
{
  forall j: int, k: int {:trigger u[k], u[j]} :: 
    0 <= j < k < |u| ==>
      u[j] != u[k]
}

method BullsCows(s: seq<nat>, u: seq<nat>)
    returns (b: nat, c: nat)
  requires 0 < |u| == |s| <= 10
  requires nomultiples(u) && nomultiples(s)
  ensures b >= 0 && c >= 0
  ensures b == bullspec(s, u)
  ensures c == cowspec(s, u)
  decreases s, u
{
  b, c := 0, 0;
  var i: int := |s|;
  while i > 0
    invariant 0 <= i <= |s| == |u|
    invariant b >= 0 && c >= 0
    invariant b == reccbull(s, u, i)
    invariant c == recccow(s, u, i)
    decreases i
  {
    i := i - 1;
    if s[i] != u[i] && u[i] in s {
      c := c + 1;
    } else if s[i] == u[i] {
      b := b + 1;
    }
  }
  return b, c;
}

method TEST()
{
}
