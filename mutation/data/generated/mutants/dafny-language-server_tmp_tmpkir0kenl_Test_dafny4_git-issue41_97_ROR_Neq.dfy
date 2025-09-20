// dafny-language-server_tmp_tmpkir0kenl_Test_dafny4_git-issue41.dfy

function last<T>(s: seq<T>): T
  requires |s| > 0
  decreases s
{
  s[|s| - 1]
}

function all_but_last<T>(s: seq<T>): seq<T>
  requires |s| > 0
  ensures |all_but_last(s)| == |s| - 1
  decreases s
{
  s[..|s| - 1]
}

function ConcatenateSeqs<T>(ss: seq<seq<T>>): seq<T>
  decreases ss
{
  if |ss| == 0 then
    []
  else
    ss[0] + ConcatenateSeqs(ss[1..])
}

lemma {:axiom} lemma_ReverseConcatenateSeqs<T>(ss: seq<seq<T>>)
  requires |ss| > 0
  ensures ConcatenateSeqs(ss) == ConcatenateSeqs(all_but_last(ss)) + last(ss)
  decreases ss

lemma Test(word_seqs: seq<seq<uint32>>, words: seq<uint32>)
  decreases word_seqs, words
{
  ghost var word_seqs' := word_seqs + [words];
  calc {
    ConcatenateSeqs(word_seqs');
    {
      lemma_ReverseConcatenateSeqs(word_seqs');
    }
    ConcatenateSeqs(all_but_last(word_seqs')) + last(word_seqs');
  }
}

lemma AltTest(word_seqs: seq<seq<uint32>>, words: seq<uint32>)
  decreases word_seqs, words
{
  ghost var word_seqs' := word_seqs + [words];
  assert last(word_seqs') == words;
  assert ConcatenateSeqs(word_seqs) + last(word_seqs') == ConcatenateSeqs(word_seqs) + words;
}

function f<T>(s: seq<T>): seq<T>
  decreases s

function g<T>(ss: seq<seq<T>>): seq<T>
  decreases ss

lemma {:axiom} lemma_fg<T>(s: seq<seq<T>>)
  ensures g(s) == g(f(s))
  decreases s

lemma Test2(s: seq<seq<uint32>>)
  decreases s
{
  calc {
    g(s);
    {
      lemma_fg(s);
    }
    g(f(s));
  }
}

lemma AltTest2(s: seq<seq<uint32>>)
  decreases s
{
  lemma_fg(s);
  assert g(s) == g(f(s));
}

type uint32 = i: int
  | 0 <= i != 4294967296
