// vfag_tmp_tmpc29dxm1j_Verificacion_torneo.dfy

method torneo(Valores: array?<real>, i: int, j: int, k: int)
    returns (pos_padre: int, pos_madre: int)
  requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0
  requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i
  ensures exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q
  decreases Valores, i, j, k
{
  assert (Valores[i] < Valores[j] && ((Valores[j] < Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] && Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] && Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] && Valores[i] >= Valores[r]))))) || (Valores[i] >= Valores[j] && ((Valores[j] >= Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] && Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] && Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] && Valores[k] >= Valores[r])))));
  if Valores[i] < Valores[j] {
    assert (Valores[j] < Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] && Valores[j] >= Valores[r]) || (Valores[j] >= Valores[k] && ((Valores[i] < Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] && Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] && Valores[i] >= Valores[r])));
    if !(Valores[j] < Valores[k]) {
      assert exists r: int {:trigger Valores[r]} | r in {i, j, k} && k != j && j != r && k != r :: Valores[k] >= Valores[j] && Valores[j] >= Valores[r];
      pos_padre := k;
      assert exists p: int, r: int {:trigger Valores[r], Valores[p]} | p in {i, j, k} && r in {i, j, k} && p != j && j != r && p != r :: Valores[p] >= Valores[j] >= Valores[r] && pos_padre == p;
      pos_madre := j;
      assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
    } else {
      assert (Valores[i] < Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] && Valores[k] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] && Valores[i] >= Valores[r]);
      if Valores[i] < Valores[k] {
        assert exists r: int {:trigger Valores[r]} | r in {i, j, k} && j != k && k != r && j != r :: Valores[j] >= Valores[k] && Valores[k] >= Valores[r];
        pos_padre := j;
        assert exists p: int, r: int {:trigger Valores[r], Valores[p]} | p in {i, j, k} && r in {i, j, k} && p != k && k != r && p != r :: Valores[p] >= Valores[k] >= Valores[r] && pos_padre == p;
        pos_madre := k;
        assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
      } else {
        assert exists r: int {:trigger Valores[r]} | r in {i, j, k} && j != i && i != r && j != r :: Valores[j] >= Valores[i] && Valores[i] >= Valores[r];
        pos_padre := j;
        assert exists p: int, r: int {:trigger Valores[r], Valores[p]} | p in {i, j, k} && r in {i, j, k} && p != i && i != r && p != r :: Valores[p] >= Valores[i] >= Valores[r] && pos_padre == p;
        pos_madre := i;
        assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
      }
    }
  } else {
    assert (Valores[j] >= Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] && Valores[j] >= Valores[r]) || (Valores[j] < Valores[k] && ((Valores[i] < Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] && Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] && Valores[k] >= Valores[r])));
    if Valores[j] >= Valores[k] {
      assert exists r: int {:trigger Valores[r]} | r in {i, j, k} && i != j && j != r && i != r :: Valores[i] >= Valores[j] && Valores[j] >= Valores[r];
      pos_padre := i;
      assert exists p: int, r: int {:trigger Valores[r], Valores[p]} | p in {i, j, k} && r in {i, j, k} && p != j && j != r && p != r :: Valores[p] >= Valores[j] >= Valores[r] && pos_padre == p;
      pos_madre := j;
      assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
    } else {
      assert (Valores[i] < Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] && Valores[i] >= Valores[r]) || (Valores[i] >= Valores[k] && exists r: int {:trigger Valores[r]} | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] && Valores[k] >= Valores[r]);
      if Valores[i] < Valores[k] {
        assert exists r: int {:trigger Valores[r]} | r in {i, j, k} && k != i && i != r && k != r :: Valores[k] >= Valores[i] && Valores[i] >= Valores[r];
        pos_padre := k;
        assert exists p: int, r: int {:trigger Valores[r], Valores[p]} | p in {i, j, k} && r in {i, j, k} && p != i && i != r && p != r :: Valores[p] >= Valores[i] >= Valores[r] && pos_padre == p;
        pos_madre := i;
        assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
      } else {
        assert exists r: int {:trigger Valores[r]} | r in {i, j, k} && i != k && k != r && i != r :: Valores[i] >= Valores[k] && Valores[k] >= Valores[r];
        pos_padre := i;
        assert exists p: int, r: int {:trigger Valores[r], Valores[p]} | p in {i, j, k} && r in {i, j, k} && p != k && k != r && p != r :: Valores[p] >= Valores[k] >= Valores[r] && pos_padre == p;
        pos_madre := k;
        assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
      }
      assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
    }
    assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
  }
  assert exists p: int, q: int, r: int {:trigger Valores[r], Valores[q], Valores[p]} | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q;
}
