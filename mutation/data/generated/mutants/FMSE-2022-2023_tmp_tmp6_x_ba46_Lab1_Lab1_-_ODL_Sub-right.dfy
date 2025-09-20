// FMSE-2022-2023_tmp_tmp6_x_ba46_Lab1_Lab1.dfy

predicate IsOddNat(x: int)
  decreases x
{
  x >= 0 &&
  x % 2 == 1
}

predicate IsEvenNat(x: int)
  decreases x
{
  x >= 0 &&
  x % 2 == 0
}

lemma AdditionOfTwoOddsResultsInEven(x: int, y: int)
  requires IsOddNat(x)
  requires IsOddNat(y)
  ensures IsEvenNat(x + y)
  decreases x, y
{
  calc {
    IsOddNat(x);
    x % 2 == 1;
  }
  calc {
    IsOddNat(y);
    y % 2 == 1;
  }
  calc {
    (x + y) % 2 == 0;
    IsEvenNat(x + y);
    true;
  }
}

predicate IsPrime(x: int)
  requires x >= 0
  decreases x
{
  x == 2 || forall d: int {:trigger x % d} :: 2 <= d < x ==> x % d != 0
}

lemma AnyPrimeGreaterThanTwoIsOdd(x: int)
  requires x > 2
  requires IsPrime(x)
  ensures IsOddNat(x)
  decreases x
{
  calc {
    x % 2;
    {
      assert forall d: int {:trigger x % d} :: 2 <= d < x ==> x % d != 0;
    }
    1;
  }
  calc {
    IsOddNat(x);
    x >= 0 &&
    x % 2 == 1;
    {
      assert x > 2;
    }
    true &&
    true;
    true;
  }
}

function add(x: int32, y: int32): int32
  decreases x, y
{
  if -2147483648 <= x as int + y as int <= 2147483647 then
    x + y
  else
    0
}

function sub(x: int32, y: int32): int32
  decreases x, y
{
  if -2147483648 <= x as int - y as int <= 2147483647 then
    x
  else
    0
}

function mul(x: int32, y: int32): int32
  decreases x, y
{
  if -2147483648 <= x as int * y as int <= 2147483647 then
    x * y
  else
    0
}

function div(x: int32, y: int32): int32
  requires y != 0
  decreases x, y
{
  if -2147483648 <= x as int / y as int <= 2147483647 then
    x / y
  else
    0
}

function mod(x: int32, y: int32): int32
  requires y != 0
  decreases x, y
{
  x % y
}

function abs(x: int32): (r: int32)
  ensures r >= 0
  decreases x
{
  if x == -2147483648 then
    0
  else if x < 0 then
    -x
  else
    x
}

newtype Odd = n: int
  | IsOddNat(n)
  witness 1

newtype Even = n: int
  | IsEvenNat(n)
  witness 2

newtype int32 = n: int
  | -2147483648 <= n < 2147483648
  witness 3
