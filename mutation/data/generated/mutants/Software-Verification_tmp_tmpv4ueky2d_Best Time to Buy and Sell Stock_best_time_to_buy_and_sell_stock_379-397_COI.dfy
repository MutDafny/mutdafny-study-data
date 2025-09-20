// Software-Verification_tmp_tmpv4ueky2d_Best Time to Buy and Sell Stock_best_time_to_buy_and_sell_stock.dfy

method best_time_to_buy_and_sell_stock(prices: array<int>) returns (max_profit: int)
  requires 1 <= prices.Length <= 100000
  requires forall i: int {:trigger prices[i]} :: (0 <= i < prices.Length ==> 0 <= prices[i]) && (0 <= i < prices.Length ==> prices[i] <= 10000)
  ensures forall i: int, j: int {:trigger prices[i], prices[j]} :: 0 <= i < j < prices.Length ==> max_profit >= prices[j] - prices[i]
  decreases prices
{
  var min_price := 10001;
  max_profit := 0;
  var i := 0;
  while !(i < prices.Length)
    invariant 0 <= i <= prices.Length
    invariant forall j: int {:trigger prices[j]} :: 0 <= j < i ==> min_price <= prices[j]
    invariant forall j: int, k: int {:trigger prices[j], prices[k]} :: 0 <= j < k < i ==> max_profit >= prices[k] - prices[j]
  {
    var price := prices[i];
    if price < min_price {
      min_price := price;
    }
    if price - min_price > max_profit {
      max_profit := price - min_price;
    }
    i := i + 1;
  }
}
