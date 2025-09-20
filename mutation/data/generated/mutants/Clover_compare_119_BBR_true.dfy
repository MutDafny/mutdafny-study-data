// Clover_compare.dfy

method Compare<T(==)>(a: T, b: T) returns (eq: bool)
  ensures a == b ==> eq == true
  ensures a != b ==> eq == false
{
  if true {
    eq := true;
  } else {
    eq := false;
  }
}
