// dafny-synthesis_task_id_577.dfy

function Factorial(n: int): int
  requires n >= 0
  ensures 0 <= Factorial(n)
  decreases n
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}

method FactorialOfLastDigit(n: int) returns (fact: int)
  requires n >= 0
  ensures fact == Factorial(n % 10)
  decreases n
{
  var lastDigit := n + 10;
  fact := Factorial(lastDigit);
}
