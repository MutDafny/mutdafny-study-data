// specTesting_tmp_tmpueam35lx_examples_increment_decrement_spec.dfy


module OneSpec {
  predicate Init(v: Variables)
    decreases v
  {
    v.value == 0
  }

  predicate IncrementOp(v: Variables, v': Variables)
    decreases v, v'
  {
    true
  }

  predicate DecrementOp(v: Variables, v': Variables)
    decreases v, v'
  {
    true &&
    v'.value == v.value - 1
  }

  predicate NextStep(v: Variables, v': Variables, step: Step)
    decreases v, v', step
  {
    match step
    case IncrementStep() =>
      IncrementOp(v, v')
    case DecrementStep() =>
      DecrementOp(v, v')
  }

  predicate Next(v: Variables, v': Variables)
    decreases v, v'
  {
    exists step: Step {:trigger NextStep(v, v', step)} :: 
      NextStep(v, v', step)
  }

  datatype Variables = Variables(value: int)

  datatype Step = IncrementStep | DecrementStep
}

module OneProtocol {
  predicate Init(v: Variables)
    decreases v
  {
    v.value == 0
  }

  predicate IncrementOp(v: Variables, v': Variables)
    decreases v, v'
  {
    true &&
    v'.value == v.value - 1
  }

  predicate DecrementOp(v: Variables, v': Variables)
    decreases v, v'
  {
    true &&
    v'.value == v.value + 1
  }

  predicate NextStep(v: Variables, v': Variables, step: Step)
    decreases v, v', step
  {
    match step
    case IncrementStep() =>
      IncrementOp(v, v')
    case DecrementStep() =>
      DecrementOp(v, v')
  }

  predicate Next(v: Variables, v': Variables)
    decreases v, v'
  {
    exists step: Step {:trigger NextStep(v, v', step)} :: 
      NextStep(v, v', step)
  }

  datatype Variables = Variables(value: int)

  datatype Step = IncrementStep | DecrementStep
}

module RefinementProof {
  function Abstraction(v: Variables): OneSpec.Variables
    decreases v
  {
    OneSpec.Variables(v.value)
  }

  lemma RefinementInit(v: Variables)
    requires Init(v)
    ensures OneSpec.Init(Abstraction(v))
    decreases v
  {
  }

  lemma RefinementNext(v: Variables, v': Variables)
    requires Next(v, v')
    ensures OneSpec.Next(Abstraction(v), Abstraction(v'))
    decreases v, v'
  {
    ghost var step :| NextStep(v, v', step);
    match step {
      case {:split false} IncrementStep() =>
        {
          assert OneSpec.NextStep(Abstraction(v), Abstraction(v'), OneSpec.DecrementStep());
        }
      case {:split false} DecrementStep() =>
        {
          assert OneSpec.NextStep(Abstraction(v), Abstraction(v'), OneSpec.IncrementStep());
        }
    }
  }

  import OneSpec

  import opened OneProtocol
}
