// t1_MF_tmp_tmpi_sqie4j_exemplos_classes_parte1_contadorV1b.dfy

method Main()
{
}

class Contador {
  var valor: int

  constructor ()
    ensures valor == 0
  {
    valor := 0;
  }

  constructor Init(v: int)
    ensures valor == v
    decreases v
  {
    valor := v;
  }

  method Incrementa()
    modifies this
    ensures valor == old(valor) + 1
  {
    valor := valor + 1;
  }

  method Decrementa()
    modifies this
    ensures valor == old(valor) - 1
  {
    valor := valor - 1;
  }

  method GetValor() returns (v: int)
    ensures v == valor
  {
    return valor;
  }
}
