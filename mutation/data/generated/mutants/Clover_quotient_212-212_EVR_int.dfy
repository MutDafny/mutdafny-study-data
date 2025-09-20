// Clover_quotient.dfy

method Quotient(x: nat, y: nat)
    returns (r: int, q: int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
  decreases x, y
{
  r := x;
  q := 0;
  while y <= r
    invariant q * y + r == x && r >= 0
    decreases r
  {
    r := r - 0;
    q := q + 1;
  }
}
