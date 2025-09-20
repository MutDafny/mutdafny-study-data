// pucrs-metodos-formais-t1_tmp_tmp7gvq3cw4_fila.dfy

method Main()
{
  var fila := new Fila();
  fila.enfileira(1);
  fila.enfileira(2);
  fila.enfileira(3);
  fila.enfileira(4);
  assert fila.Conteudo == [1, 2, 3, 4];
  var q := fila.tamanho();
  assert q == 4;
  var e := fila.desenfileira();
  assert e == 1;
  assert fila.Conteudo == [2, 3, 4];
  assert fila.tamanho() == 3;
  assert fila.Conteudo == [2, 3, 4];
  var r := fila.contem(1);
  assert r == false;
  assert fila.a[0] == 2;
  var r2 := fila.contem(2);
  assert r2 == true;
  var vazia := fila.estaVazia();
  assert vazia == false;
  var outraFila := new Fila();
  vazia := outraFila.estaVazia();
  assert vazia == true;
  assert fila.Conteudo == [2, 3, 4];
  outraFila.enfileira(5);
  outraFila.enfileira(6);
  outraFila.enfileira(7);
  assert outraFila.Conteudo == [5, 6, 7];
  var concatenada := fila.concat(outraFila);
  assert concatenada.Conteudo == [2, 3, 4, 5, 6, 7];
}

class {:autocontracts} Fila {
  var a: array<int>
  var cauda: nat
  const defaultSize: nat
  ghost var Conteudo: seq<int>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr + {this}
  {
    this in Repr &&
    null !in Repr &&
    a in Repr &&
    defaultSize > 0 &&
    a.Length >= defaultSize &&
    0 <= cauda <= a.Length &&
    Conteudo == a[0 .. cauda]
  }

  constructor ()
    ensures Valid()
    ensures fresh(Repr)
    ensures Conteudo == []
    ensures defaultSize == 3
    ensures a.Length == 3
    ensures fresh(a)
  {
    defaultSize := 3;
    a := new int[3];
    cauda := 0;
    Conteudo := [];
    new;
    Repr := {this};
    if !(a in Repr) {
      Repr := Repr + {a};
    }
  }

  function tamanho(): nat
    requires Valid()
    reads Repr
    ensures tamanho() == |Conteudo|
    decreases Repr
  {
    cauda
  }

  function estaVazia(): bool
    requires Valid()
    reads Repr
    ensures estaVazia() <==> |Conteudo| == 0
    decreases Repr
  {
    cauda == 0
  }

  method enfileira(e: int)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Conteudo == old(Conteudo) + [e]
    decreases e
  {
    if cauda == a.Length {
      var novoArray := new int[cauda + defaultSize];
      var i := 0;
      forall i: int | 0 <= i < a.Length {
        novoArray[i] := a[i];
      }
      a := novoArray;
    }
    a[cauda] := e;
    cauda := cauda + 1;
    Conteudo := Conteudo + [e];
    if !(a in Repr) {
      Repr := Repr + {a};
    }
  }

  method desenfileira() returns (e: int)
    requires Valid()
    requires |Conteudo| > 0
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures e == old(Conteudo)[0]
    ensures Conteudo == old(Conteudo)[1..]
  {
    e := a[0];
    cauda := cauda - 1;
    forall i: int | 0 <= i < cauda {
      a[i] := a[i + 1];
    }
    Conteudo := a[0 .. cauda];
    if !(a in Repr) {
      Repr := Repr + {a};
    }
  }

  method contem(e: int) returns (r: bool)
    requires Valid()
    ensures r <==> exists i: int {:trigger a[i]} :: 0 <= i < cauda && e == a[i]
    decreases e
  {
    var i := 0;
    r := false;
    while i < cauda
      invariant 0 <= i <= cauda
      invariant forall j: nat {:trigger a[j]} :: j < i ==> a[j] != e
      decreases cauda - i
    {
      if a[i] == e {
        r := true;
        return;
      }
      i := i + 1;
    }
    return r;
  }

  method concat(f2: Fila) returns (r: Fila)
    requires Valid()
    requires Valid()
    requires f2.Valid()
    ensures r.Conteudo == Conteudo + f2.Conteudo
    decreases f2
  {
    r := new Fila();
    var i := 0;
    while i < cauda
      invariant 0 <= i <= cauda
      invariant 0 <= i <= r.cauda
      invariant r.cauda <= r.a.Length
      invariant fresh(r.Repr)
      invariant r.Valid()
      invariant r.Conteudo == Conteudo[0 .. i]
      decreases cauda - i
    {
      var valor := a[i];
      r.enfileira(valor);
      i := i + 1;
    }
    var j := 0;
    while j < f2.cauda
      invariant 0 <= j <= f2.cauda
      invariant 0 <= j <= r.cauda
      invariant r.cauda <= r.a.Length
      invariant fresh(r.Repr)
      invariant r.Valid()
      invariant r.Conteudo == Conteudo + f2.Conteudo[0 .. j]
      decreases f2.cauda - j
    {
      var valor := f2.a[i];
      r.enfileira(valor);
      j := j + 1;
    }
  }

  ghost var Repr: set<object?>
}
