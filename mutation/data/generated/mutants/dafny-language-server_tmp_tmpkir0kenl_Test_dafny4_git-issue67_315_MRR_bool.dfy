// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue67.dfy

predicate Q(x: Node)
  decreases x

predicate P(x: Node)
  decreases x

method AuxMethod(y: Node)
  modifies y
  decreases y

method MainMethod(y: Node)
  modifies y
  decreases y
{
  AuxMethod(y);
  forall x: Node | false
    ensures P(x)
  {
    assume false;
  }
  assert forall x: Node {:trigger P(x)} {:trigger Q(x)} :: Q(x) ==> P(x);
}

class Node { }
