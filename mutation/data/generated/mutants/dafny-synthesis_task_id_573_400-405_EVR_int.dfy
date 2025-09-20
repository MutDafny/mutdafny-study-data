// dafny-synthesis_task_id_573.dfy

method UniqueProduct(arr: array<int>) returns (product: int)
  ensures product == SetProduct(set i: int {:trigger arr[i]} | 0 <= i < arr.Length :: arr[i])
  decreases arr
{
  var p := 1;
  var seen: set<int> := {};
  for i: int := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant seen == set k: int {:trigger arr[k]} | 0 <= k < i :: arr[k]
    invariant p == SetProduct(set k: int {:trigger arr[k]} | 0 <= k < i :: arr[k])
  {
    if !(0 in seen) {
      seen := seen + {arr[i]};
      p := p * arr[i];
      SetProductLemma(seen, arr[i]);
    }
  }
  product := p;
}

ghost function SetProduct(s: set<int>): int
  decreases s
{
  if s == {} then
    1
  else
    ghost var x: int /*{:_delayTriggerWarning}*/ {:trigger x in s} :| x in s; x * SetProduct(s - {x})
}

lemma /*{:_inductionTrigger s - {x}}*/ /*{:_inductionTrigger x in s}*/ /*{:_induction s}*/ SetProductLemma(s: set<int>, x: int)
  requires x in s
  ensures SetProduct(s - {x}) * x == SetProduct(s)
  decreases s, x
{
  if s != {} {
    ghost var y :| y in s && y * SetProduct(s - {y}) == SetProduct(s);
    if y == x {
    } else {
      calc {
        SetProduct(s);
        y * SetProduct(s - {y});
        {
          SetProductLemma(s - {y}, x);
        }
        y * x * SetProduct(s - {y} - {x});
        {
          assert s - {x} - {y} == s - {y} - {x};
        }
        y * x * SetProduct(s - {x} - {y});
        x * y * SetProduct(s - {x} - {y});
        {
          SetProductLemma(s - {x}, y);
        }
        x * SetProduct(s - {x});
      }
    }
  }
}
