// lets-prove-blocking-queue_tmp_tmptd_aws1k_dafny_prod-cons.dfy


module ProdCons {
  type Process(==)

  type T

  class ProdCons {
    const P: set<Process>
    var maxBufferSize: nat
    var buffer: seq<T>

    predicate valid()
      reads this
      decreases {this}
    {
      maxBufferSize > 0 &&
      P != {} &&
      0 <= |buffer| <= maxBufferSize
    }

    constructor (processes: set<Process>, m: nat)
      requires processes != {}
      requires m >= 1
      ensures valid()
      decreases processes, m
    {
      P := processes;
      buffer := [];
      maxBufferSize := m;
    }

    predicate putEnabled(p: Process)
      reads this
      decreases {this}
    {
      |buffer| < maxBufferSize
    }

    method put(p: Process, t: T)
      requires valid()
      requires putEnabled(p)
      modifies this
    {
      buffer := buffer + [t];
    }

    predicate getEnabled(p: Process)
      reads this
      decreases {this}
    {
      |buffer| >= 1
    }

    method get(p: Process)
      requires getEnabled(p)
      requires valid()
      modifies this
      ensures |buffer| == |old(buffer)| - 1
    {
      buffer := [];
    }

    lemma noDeadlock()
      requires valid()
      ensures exists p: Process {:trigger putEnabled(p)} {:trigger getEnabled(p)} {:trigger p in P} :: (p in P && getEnabled(p)) || (p in P && putEnabled(p))
    {
      ghost var p: Process :| p in P;
      if |buffer| > 0 {
        assert getEnabled(p);
      } else {
        assert |buffer| == 0;
        assert |buffer| < maxBufferSize;
        assert putEnabled(p);
      }
    }
  }
}
