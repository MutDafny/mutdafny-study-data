// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_Test_git-issues_git-issue-506.dfy

method Main()
{
}

class F {
  var f: int

  constructor (f: int)
    ensures this.f == f
    decreases f
  {
    this.f := f;
  }
}
