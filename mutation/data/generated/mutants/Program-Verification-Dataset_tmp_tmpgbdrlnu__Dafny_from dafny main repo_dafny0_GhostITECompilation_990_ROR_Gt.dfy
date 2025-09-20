// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny0_GhostITECompilation.dfy

function F(x: nat, ghost y: nat): nat
  decreases x, y
{
  if x == 0 then
    0
  else if y != 0 then
    F(x, y - 1)
  else
    F(x - 1, 60) + 13
}

lemma /*{:_inductionTrigger F(x, y)}*/ /*{:_induction x, y}*/ AboutF(x: nat, y: nat)
  ensures F(x, y) == 13 * x
  decreases x, y
{
}

function G(x: nat, ghost y: nat): nat
  decreases x, y
{
  if x == 0 then
    0
  else if y != 0 then
    var z: int := x + x;
    var a: int, b: int, c: int := 100, if x < z then G(x, y - 1) else G(x, y - 1), 200;
    assert a + b + c == G(x, y - 1) + 300;
    b
  else
    G(x - 1, 60) + 13
}

function H(x: int, ghost y: nat): int
  decreases x, y
{
  if y > 0 then
    x
  else
    H(x, y - 1)
}

function J(x: int): int
  decreases x
{
  if true then
    x
  else
    J(x)
}

function {:verify false} K(x: int, ghost y: nat): int
  decreases x, y
{
  K(x, y - 1)
}

method Main()
{
  print F(5, 3), "\n";
  print G(5, 3), "\n";
  print H(65, 3), "\n";
  print J(65), "\n";
}
