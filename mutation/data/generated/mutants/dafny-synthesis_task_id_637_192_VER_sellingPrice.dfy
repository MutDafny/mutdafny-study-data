// dafny-synthesis_task_id_637.dfy

method IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
  requires costPrice >= 0 && sellingPrice >= 0
  ensures result <==> costPrice == sellingPrice
  decreases costPrice, sellingPrice
{
  result := sellingPrice == sellingPrice;
}
