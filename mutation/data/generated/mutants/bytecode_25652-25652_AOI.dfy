// bytecode.dfy


module Bytecode {
  function Stop(st: ExecutingState): State
    decreases st
  {
    RETURNS(gas := st.Gas(), data := [], world := st.evm.world, transient := st.evm.transient, substate := st.evm.substate)
  }

  function Add(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: int := st.Peek(0) as int;
      var rhs: int := st.Peek(1) as int;
      var res: int := (lhs + rhs) % TWO_256;
      st.Pop(2).Push(res as u256).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Mul(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: int := st.Peek(0) as int;
      var rhs: int := st.Peek(1) as int;
      var res: int := lhs * rhs % TWO_256;
      st.Pop(2).Push(res as u256).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Sub(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: int := st.Peek(0) as int;
      var rhs: int := st.Peek(1) as int;
      var res: int := (lhs - rhs) % TWO_256;
      st.Pop(2).Push(res as u256).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function DivWithZero(lhs: u256, rhs: u256): u256
    decreases lhs, rhs
  {
    if rhs == 0 then
      0 as u256
    else
      (lhs / rhs) as u256
  }

  function ModWithZero(lhs: u256, rhs: u256): u256
    decreases lhs, rhs
  {
    if rhs == 0 then
      0 as u256
    else
      (lhs % rhs) as u256
  }

  function SDivWithZero(lhs: i256, rhs: i256): i256
    decreases lhs, rhs
  {
    if rhs == 0 then
      0 as i256
    else if rhs == -1 && lhs == -TWO_255 as i256 then
      -TWO_255 as i256
    else
      I256.Div(lhs, rhs)
  }

  function SModWithZero(lhs: i256, rhs: i256): i256
    decreases lhs, rhs
  {
    if rhs == 0 then
      0 as i256
    else
      I256.Rem(lhs, rhs)
  }

  function Div(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: u256 := st.Peek(0);
      var rhs: u256 := st.Peek(1);
      var res: u256 := DivWithZero(lhs, rhs) as u256;
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function SDiv(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: i256 := Word.asI256(st.Peek(0));
      var rhs: i256 := Word.asI256(st.Peek(1));
      var res: u256 := Word.fromI256(SDivWithZero(lhs, rhs));
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Mod(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: u256 := st.Peek(0);
      var rhs: u256 := st.Peek(1);
      var res: u256 := ModWithZero(lhs, rhs) as u256;
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function SMod(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: i256 := Word.asI256(st.Peek(0));
      var rhs: i256 := Word.asI256(st.Peek(1));
      var res: u256 := Word.fromI256(SModWithZero(lhs, rhs));
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function AddMod(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    decreases st
  {
    if st.Operands() >= 3 then
      var lhs: int := st.Peek(0) as int;
      var rhs: int := st.Peek(1) as int;
      var rem: int := st.Peek(2) as int;
      var res: int := if rem == 0 then 0 else (lhs + rhs) % rem;
      st.Pop(3).Push(res as u256).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function MulMod(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    decreases st
  {
    if st.Operands() >= 3 then
      var lhs: int := st.Peek(0) as int;
      var rhs: int := st.Peek(1) as int;
      var rem: int := st.Peek(2) as int;
      var res: int := if rem == 0 then 0 else lhs * rhs % rem;
      st.Pop(3).Push(res as u256).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Exp(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var base: int := st.Peek(0) as int;
      var power: int := st.Peek(1) as int;
      var res: int := MathUtils.Pow(base, power) % TWO_256;
      st.Pop(2).Push(res as u256).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function SignExtend(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var width: u256 := st.Peek(0);
      var item: u256 := st.Peek(1);
      var res: u256 := U256.SignExtend(item, width as nat);
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Lt(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: u256 := st.Peek(0);
      var rhs: u256 := st.Peek(1);
      if lhs < rhs then
        st.Pop(2).Push(1).Next()
      else
        st.Pop(2).Push(0).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Gt(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: u256 := st.Peek(0);
      var rhs: u256 := st.Peek(1);
      if lhs > rhs then
        st.Pop(2).Push(1).Next()
      else
        st.Pop(2).Push(0).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function SLt(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: i256 := Word.asI256(st.Peek(0));
      var rhs: i256 := Word.asI256(st.Peek(1));
      if lhs < rhs then
        st.Pop(2).Push(1).Next()
      else
        st.Pop(2).Push(0).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function SGt(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: i256 := Word.asI256(st.Peek(0));
      var rhs: i256 := Word.asI256(st.Peek(1));
      if lhs > rhs then
        st.Pop(2).Push(1).Next()
      else
        st.Pop(2).Push(0).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Eq(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: u256 := st.Peek(0);
      var rhs: u256 := st.Peek(1);
      if lhs == rhs then
        st.Pop(2).Push(1).Next()
      else
        st.Pop(2).Push(0).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function IsZero(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var mhs: u256 := st.Peek(0);
      if mhs == 0 then
        st.Pop().Push(1).Next()
      else
        st.Pop().Push(0).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function {:verify false} And(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: bv256 := st.Peek(0) as bv256;
      var rhs: bv256 := st.Peek(1) as bv256;
      var res: u256 := (lhs & rhs) as u256;
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Or(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: bv256 := st.Peek(0) as bv256;
      var rhs: bv256 := st.Peek(1) as bv256;
      U256.as_bv256_as_u256(lhs | rhs);
      var res: u256 := (lhs | rhs) as u256;
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function {:verify false} Xor(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var lhs: bv256 := st.Peek(0) as bv256;
      var rhs: bv256 := st.Peek(1) as bv256;
      U256.as_bv256_as_u256(lhs ^ rhs);
      var res: u256 := (lhs ^ rhs) as u256;
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Not(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var mhs: bv256 := st.Peek(0) as bv256;
      var res: u256 := !mhs as u256;
      st.Pop().Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Byte(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var val: u256 := st.Peek(1);
      var k: nat := st.Peek(0) as nat;
      var res: u8 := if k < 32 then U256.NthUint8(val, k) else 0 as u8;
      st.Pop(2).Push(res as u256).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Shl(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var rhs: u256 := st.Peek(0);
      var lhs: u256 := st.Peek(1);
      var res: u256 := U256.Shl(lhs, rhs);
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Shr(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var rhs: u256 := st.Peek(0);
      var lhs: u256 := st.Peek(1);
      var res: u256 := U256.Shr(lhs, rhs);
      st.Pop(2).Push(res).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Sar(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var rhs: u256 := st.Peek(0);
      var lhs: i256 := Word.asI256(st.Peek(1));
      var res: i256 := I256.Sar(lhs, rhs);
      st.Pop(2).Push(Word.fromI256(res)).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Keccak256(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 2 then
      var loc: nat := st.Peek(0) as nat;
      var len: nat := st.Peek(1) as nat;
      var bytes: seq<u8> := Memory.Slice(st.evm.memory, loc, len);
      var hash: u256 := st.evm.precompiled.Sha3(bytes);
      st.Expand(loc, len).Pop(2).Push(hash).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function BlockHash(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var n: u256 := st.Peek(0);
      st.Pop().Push(0).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Address(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.address as u256).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function Balance(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var account: u160 := (st.Peek(0) as nat % TWO_160) as u160;
      var balance: u256 := if st.evm.world.Exists(account) then st.evm.world.Balance(account) else 0;
      st.AccountAccessed(account).Pop().Push(balance).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Origin(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.origin as u256).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function Caller(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.sender as u256).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function CallValue(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.callValue).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function CallDataLoad(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var loc: u256 := st.Peek(0);
      var val: u256 := if loc >= st.evm.context.CallDataSize() then 0 else st.evm.context.CallDataRead(loc);
      st.Pop().Push(val).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function CallDataSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      var len: u256 := st.evm.context.CallDataSize();
      st.Push(len).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function CallDataCopy(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 3
    decreases st
  {
    if st.Operands() >= 3 then
      var m_loc: nat := st.Peek(0) as nat;
      var d_loc: u256 := st.Peek(1);
      var len: nat := st.Peek(2) as nat;
      var data: seq<u8> := st.evm.context.CallDataSlice(d_loc, len as nat);
      assert |data| == len;
      st.Expand(m_loc as nat, len as nat).Pop(3).Copy(m_loc, data).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function CodeSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(Code.Size(st.evm.code)).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function CodeCopy(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 3
    decreases st
  {
    if st.Operands() >= 3 then
      var m_loc: nat := st.Peek(0) as nat;
      var d_loc: nat := st.Peek(1) as nat;
      var len: nat := st.Peek(2) as nat;
      var last: int := m_loc as nat + -len;
      var data: seq<u8> := Code.Slice(st.evm.code, d_loc, len);
      assert |data| == len;
      st.Expand(m_loc as nat, len).Pop(3).Copy(m_loc, data).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function GasPrice(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.gasPrice).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function ExtCodeSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var account: u160 := (st.Peek(0) as nat % TWO_160) as u160;
      if st.IsDead(account) then
        st.AccountAccessed(account).Pop().Push(0).Next()
      else
        var data: Account := st.evm.world.GetOrDefault(account); var size: u256 := |data.code.contents| as u256; st.AccountAccessed(account).Pop().Push(size).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function ExtCodeCopy(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 4
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 4
    decreases st
  {
    if st.Operands() >= 4 then
      var address: u160 := (st.Peek(0) as nat % TWO_160) as u160;
      var m_loc: nat := st.Peek(1) as nat;
      var d_loc: nat := st.Peek(2) as nat;
      var len: nat := st.Peek(3) as nat;
      var last: int := m_loc as nat + len;
      var account: Account := st.evm.world.GetOrDefault(address);
      var data: seq<u8> := Code.Slice(account.code, d_loc, len);
      assert |data| == len;
      st.AccountAccessed(address).Expand(m_loc as nat, len).Pop(4).Copy(m_loc, data).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function ExtCodeHash(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var account: u160 := (st.Peek(0) as nat % TWO_160) as u160;
      if st.IsDead(account) then
        st.AccountAccessed(account).Pop().Push(0).Next()
      else
        var data: Account := st.evm.world.GetAccount(account).Unwrap(); st.AccountAccessed(account).Pop().Push(data.hash).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function ReturnDataSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      var len: u256 := st.evm.context.ReturnDataSize();
      st.Push(len).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function ReturnDataCopy(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(RETURNDATA_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 3 && st.Peek(1) as nat + st.Peek(2) as nat <= st.evm.context.ReturnDataSize() as nat
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 3
    decreases st
  {
    if st.Operands() >= 3 then
      var m_loc: nat := st.Peek(0) as nat;
      var d_loc: nat := st.Peek(1) as nat;
      var len: nat := st.Peek(2) as nat;
      if d_loc + len <= st.evm.context.ReturnDataSize() as nat then
        var data: seq<u8> := st.evm.context.ReturnDataSlice(d_loc, len);
        assert |data| == len;
        st.Expand(m_loc, len).Pop(3).Copy(m_loc, data).Next()
      else
        ERROR(RETURNDATA_OVERFLOW)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function CoinBase(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.block.coinBase).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function TimeStamp(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.block.timeStamp).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function Number(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.block.number).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function Difficulty(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.block.difficulty).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function GasLimit(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.block.gasLimit).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function ChainID(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.block.chainID).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function SelfBalance(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      var address: u160 := st.evm.context.address;
      var balance: u256 := st.evm.world.Balance(address);
      st.Push(balance).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function BaseFee(st: ExecutingState): (st': State)
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(st.evm.context.block.baseFee).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function Pop(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 1 then
      st.Pop().Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function MSize(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW) || st' == ERROR(MEMORY_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1 && Memory.Size(st.evm.memory) <= MAX_U256
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      var s: nat := Memory.Size(st.evm.memory);
      if s <= MAX_U256 then
        st.Push(s as u256).Next()
      else
        ERROR(MEMORY_OVERFLOW)
    else
      ERROR(STACK_OVERFLOW)
  }

  function MLoad(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var loc: nat := st.Peek(0) as nat;
      var nst: ExecutingState := st.Expand(loc, 32);
      nst.Pop().Push(nst.Read(loc)).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function MStore(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    decreases st
  {
    if st.Operands() >= 2 then
      var loc: nat := st.Peek(0) as nat;
      var val: u256 := st.Peek(1);
      st.Expand(loc, 32).Pop(2).Write(loc, val).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function MStore8(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 2
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    decreases st
  {
    if st.Operands() >= 2 then
      var loc: nat := st.Peek(0) as nat;
      var val: u8 := (st.Peek(1) % 256) as u8;
      st.Expand(loc, 1).Pop(2).Write8(loc, val).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function SLoad(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.EXECUTING? <==> st.Operands() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st
  {
    if st.Operands() >= 1 then
      var loc: u256 := st.Peek(0);
      var val: u256 := st.Load(loc);
      st.Pop().Push(val).KeyAccessed(loc).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function SStore(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.EXECUTING? <==> st.Operands() >= 2 && st.WritesPermitted()
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    decreases st
  {
    if st.Operands() >= 2 then
      if !st.WritesPermitted() then
        ERROR(WRITE_PROTECTION_VIOLATED)
      else
        var loc: u256 := st.Peek(0); var val: u256 := st.Peek(1); st.Pop(2).Store(loc, val).KeyAccessed(loc).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Jump(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(INVALID_JUMPDEST)
    ensures st'.EXECUTING? <==> st.Operands() >= 1 && st.IsJumpDest(st.Peek(0))
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 1
    decreases st
  {
    if st.Operands() >= 1 then
      var pc: u256 := st.Peek(0);
      if st.IsJumpDest(pc) then
        st.Pop().Goto(pc)
      else
        ERROR(INVALID_JUMPDEST)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function JumpI(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(INVALID_JUMPDEST)
    ensures st'.EXECUTING? <==> st.Operands() >= 2 && (st.Peek(1) == 0 || st.IsJumpDest(st.Peek(0)))
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - 2
    decreases st
  {
    if st.Operands() >= 2 then
      var pc: u256 := st.Peek(0);
      var val: u256 := st.Peek(1);
      if val == 0 then
        st.Pop(2).Next()
      else if st.IsJumpDest(pc) then
        st.Pop(2).Goto(pc)
      else
        ERROR(INVALID_JUMPDEST)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Pc(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1 && st.PC() <= MAX_U256
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 && st.PC() <= MAX_U256 then
      st.Push(st.PC() as u256).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function Gas(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1 && st.Gas() <= MAX_U256 as nat
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 && st.Gas() <= MAX_U256 as nat then
      st.Push(st.Gas() as u256).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function JumpDest(st: ExecutingState): (st': ExecutingState)
    decreases st
  {
    st.Next()
  }

  function TLoad(st: ExecutingState): (st': State)
    decreases st
  {
    if st.Operands() >= 1 then
      var loc: u256 := st.Peek(0);
      var val: u256 := st.TransientLoad(loc);
      st.Pop().Push(val).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function TStore(st: ExecutingState): (st': State)
    decreases st
  {
    if st.Operands() >= 2 then
      if !st.WritesPermitted() then
        ERROR(WRITE_PROTECTION_VIOLATED)
      else
        var loc: u256 := st.Peek(0); var val: u256 := st.Peek(1); st.Pop(2).TransientStore(loc, val).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function MCopy(st: ExecutingState): (st': State)
    decreases st
  {
    if st.Operands() >= 3 then
      var dst: nat := st.Peek(0) as nat;
      var src: nat := st.Peek(1) as nat;
      var len: nat := st.Peek(2) as nat;
      var data: seq<u8> := Memory.Slice(st.evm.memory, src, len);
      assert |data| == len;
      st.Expand(src, len).Expand(dst, len).Pop(3).Copy(dst, data).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function RJump(st: ExecutingState, offset: i16): (st': State)
    decreases st, offset
  {
    var post_pc: int := (st.evm.pc + 3) as int;
    var target: int := post_pc + offset as int;
    if st.IsInstructionBoundary(target) then
      st.Goto(target as u256)
    else
      ERROR(INVALID_JUMPDEST)
  }

  function RJumpI(st: ExecutingState, offset: i16): (st': State)
    decreases st, offset
  {
    if st.Operands() >= 1 then
      var val: u256 := st.Peek(0);
      if val == 0 then
        st.Pop(1).Next()
      else
        var post_pc: int := (st.evm.pc + 3) as int; var target: int := post_pc + offset as int; if st.IsInstructionBoundary(target) then st.Pop(1).Goto(target as u256) else ERROR(INVALID_JUMPDEST)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function RJumpV(st: ExecutingState, table: seq<i16>): (st': State)
    requires 1 <= |table| <= 255
    decreases st, table
  {
    if st.Operands() >= 1 then
      var val: nat := st.Peek(0) as nat;
      if val >= |table| then
        st.Pop(1).Next()
      else
        var post_pc: int := (st.evm.pc + 3) as int; var target: int := post_pc + table[val] as int; if st.IsInstructionBoundary(target) then st.Pop(1).Goto(target as u256) else ERROR(INVALID_JUMPDEST)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Push0(st: ExecutingState): (st': State)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st
  {
    if st.Capacity() >= 1 then
      st.Push(0).Next()
    else
      ERROR(STACK_OVERFLOW)
  }

  function Push(st: ExecutingState, k: nat): (st': State)
    requires k > 0 && k <= 32
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st, k
  {
    if st.Capacity() >= 1 then
      var bytes: seq<u8> := Code.Slice(st.evm.code, st.evm.pc + 1, k);
      assert 0 < |bytes| <= 32;
      var val: u256 := ByteUtils.ConvertBytesTo256(bytes);
      st.Push(val).Skip(|bytes| + 1)
    else
      ERROR(STACK_OVERFLOW)
  }

  function Push1(st: ExecutingState, k: u8): (st': State)
    decreases st, k
  {
    PushN(st, 1, k as u256)
  }

  function Push2(st: ExecutingState, k: u16): (st': State)
    decreases st, k
  {
    PushN(st, 2, k as u256)
  }

  function Push3(st: ExecutingState, k: u24): (st': State)
    decreases st, k
  {
    PushN(st, 3, k as u256)
  }

  function Push4(st: ExecutingState, k: u32): (st': State)
    decreases st, k
  {
    PushN(st, 4, k as u256)
  }

  function Push5(st: ExecutingState, k: u40): (st': State)
    decreases st, k
  {
    PushN(st, 5, k as u256)
  }

  function Push6(st: ExecutingState, k: u48): (st': State)
    decreases st, k
  {
    PushN(st, 6, k as u256)
  }

  function Push7(st: ExecutingState, k: u56): (st': State)
    decreases st, k
  {
    PushN(st, 7, k as u256)
  }

  function Push8(st: ExecutingState, k: u64): (st': State)
    decreases st, k
  {
    PushN(st, 8, k as u256)
  }

  function PushN(st: ExecutingState, n: nat, k: u256): (st': State)
    requires 1 <= n <= 32
    requires k as nat <= Int.MaxUnsignedN(n)
    ensures st'.EXECUTING? || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st, n, k
  {
    if st.Capacity() >= 1 then
      st.Push(k as u256).Skip(n + 1)
    else
      ERROR(STACK_OVERFLOW)
  }

  function Dup(st: ExecutingState, k: nat): (st': State)
    requires k > 0
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(STACK_OVERFLOW)
    ensures st'.EXECUTING? <==> st.Capacity() >= 1 && st.Operands() >= k
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() + 1
    decreases st, k
  {
    if st.Capacity() < 1 then
      ERROR(STACK_OVERFLOW)
    else if st.Operands() > k - 1 then
      var kth: u256 := st.Peek(k - 1);
      st.Push(kth).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Swap(st: ExecutingState, k: nat): (st': State)
    requires 1 <= k <= 16
    ensures st'.EXECUTING? <==> st.Operands() > k
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands()
    decreases st, k
  {
    if st.Operands() > k then
      st.Swap(k).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function LogN(st: ExecutingState, n: nat): (st': State)
    requires n <= 4
    ensures st'.EXECUTING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.EXECUTING? <==> st.Operands() >= n + 2 && st.WritesPermitted()
    ensures st'.EXECUTING? ==> st'.Operands() == st.Operands() - (n + 2)
    decreases st, n
  {
    if st.Operands() >= n + 2 then
      if !st.WritesPermitted() then
        ERROR(WRITE_PROTECTION_VIOLATED)
      else
        var m_loc: nat := st.Peek(0) as nat; var len: nat := st.Peek(1) as nat; var entry: (seq<u256>, seq<u8>) := (st.PeekN(n + 2)[2..], Memory.Slice(st.evm.memory, m_loc, len)); st.Expand(m_loc, len).Log([entry]).Pop(n + 2).Next()
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Create(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st'.EXECUTING? || st' in {ERROR(STACK_UNDERFLOW), ERROR(WRITE_PROTECTION_VIOLATED), ERROR(INSUFFICIENT_GAS)}
    decreases st
  {
    if st.Operands() >= 3 then
      var endowment: u256 := st.Peek(0);
      var codeOffset: nat := st.Peek(1) as nat;
      var codeSize: nat := st.Peek(2) as nat;
      if !st.WritesPermitted() then
        ERROR(WRITE_PROTECTION_VIOLATED)
      else if st.IsEipActive(3860) && codeSize > 2 * Code.MAX_CODE_SIZE then
        ERROR(INSUFFICIENT_GAS)
      else
        var code: seq<u8> := Memory.Slice(st.evm.memory, codeOffset, codeSize); var gascap: nat := GasCalc.CreateGasCap(st); var nst: ExecutingState := st.Expand(codeOffset, codeSize).Pop(3).Next(); if st.evm.world.Nonce(st.evm.context.address) < MAX_U64 then var nnst: ExecutingState := nst.UseGas(gascap).IncNonce(); CONTINUING(CREATES(nnst.evm, gascap, endowment, code, None)) else nst.Push(0)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Call(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.CONTINUING? <==> st.Operands() >= 7 && (st.WritesPermitted() || st.Peek(2) == 0)
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 7
    ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==> st.Operands() >= 7 && !st.WritesPermitted() && st.Peek(2) > 0
    decreases st
  {
    if st.Operands() >= 7 then
      var outSize: nat := st.Peek(6) as nat;
      var outOffset: nat := st.Peek(5) as nat;
      var inSize: nat := st.Peek(4) as nat;
      var inOffset: nat := st.Peek(3) as nat;
      var value: u256 := st.Peek(2);
      var to: u160 := (st.Peek(1) as int % TWO_160) as u160;
      var gas: nat := st.Peek(0) as nat;
      var gascap: nat := GasCalc.CallGasCap(st, gas);
      var callgas: nat := GasCalc.CallGas(st, gas, value);
      if !st.WritesPermitted() && value != 0 then
        ERROR(WRITE_PROTECTION_VIOLATED)
      else
        var calldata: seq<u8> := Memory.Slice(st.evm.memory, inOffset, inSize); var address: u160 := st.evm.context.address; var nst: ExecutingState := st.AccountAccessed(to).UseGas(gascap).Expand(inOffset, inSize).Expand(outOffset, outSize).Pop(7).Next(); CONTINUING(CALLS(nst.evm, address, to, to, callgas, value, value, calldata, st.evm.context.writePermission, outOffset := outOffset, outSize := outSize))
    else
      ERROR(STACK_UNDERFLOW)
  }

  function CallCode(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.CONTINUING? <==> st.Operands() >= 7
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 7
    decreases st
  {
    if st.Operands() >= 7 then
      var outSize: nat := st.Peek(6) as nat;
      var outOffset: nat := st.Peek(5) as nat;
      var inSize: nat := st.Peek(4) as nat;
      var inOffset: nat := st.Peek(3) as nat;
      var value: u256 := st.Peek(2);
      var to: u160 := (st.Peek(1) as int % TWO_160) as u160;
      var gas: nat := st.Peek(0) as nat;
      var gascap: nat := GasCalc.CallGasCap(st, gas);
      var callgas: nat := GasCalc.CallGas(st, gas, value);
      var calldata: seq<u8> := Memory.Slice(st.evm.memory, inOffset, inSize);
      var address: u160 := st.evm.context.address;
      var nst: ExecutingState := st.AccountAccessed(to).UseGas(gascap).Expand(inOffset, inSize).Expand(outOffset, outSize).Pop(7).Next();
      CONTINUING(CALLS(nst.evm, address, address, to, callgas, value, value, calldata, nst.evm.context.writePermission, outOffset := outOffset, outSize := outSize))
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Return(st: ExecutingState): (st': State)
    ensures st'.RETURNS? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.RETURNS? <==> st.Operands() >= 2
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 2
    decreases st
  {
    if st.Operands() >= 2 then
      var len: nat := st.Peek(1) as nat;
      var start: nat := st.Peek(0) as nat;
      var data: seq<u8> := Memory.Slice(st.evm.memory, start, len);
      RETURNS(gas := st.evm.gas, data := data, world := st.evm.world, transient := st.evm.transient, substate := st.evm.substate)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function DelegateCall(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.CONTINUING? <==> st.Operands() >= 6
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 6
    decreases st
  {
    if st.Operands() >= 6 then
      var outSize: nat := st.Peek(5) as nat;
      var outOffset: nat := st.Peek(4) as nat;
      var inSize: nat := st.Peek(3) as nat;
      var inOffset: nat := st.Peek(2) as nat;
      var to: u160 := (st.Peek(1) as int % TWO_160) as u160;
      var gas: nat := st.Peek(0) as nat;
      var gascap: nat := GasCalc.CallGasCap(st, gas);
      var callgas: nat := GasCalc.CallGas(st, gas, 0);
      var calldata: seq<u8> := Memory.Slice(st.evm.memory, inOffset, inSize);
      var callValue: u256 := st.evm.context.callValue;
      var sender: u160 := st.evm.context.sender;
      var address: u160 := st.evm.context.address;
      var nst: ExecutingState := st.AccountAccessed(to).UseGas(gascap).Expand(inOffset, inSize).Expand(outOffset, outSize).Pop(6).Next();
      CONTINUING(CALLS(nst.evm, sender, address, to, callgas, 0, callValue, calldata, nst.evm.context.writePermission, outOffset := outOffset, outSize := outSize))
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Create2(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st'.EXECUTING? || st' in {ERROR(STACK_UNDERFLOW), ERROR(WRITE_PROTECTION_VIOLATED), ERROR(INSUFFICIENT_GAS)}
    decreases st
  {
    if st.Operands() >= 4 then
      var endowment: u256 := st.Peek(0);
      var codeOffset: nat := st.Peek(1) as nat;
      var codeSize: nat := st.Peek(2) as nat;
      var salt: u256 := st.Peek(3);
      if !st.WritesPermitted() then
        ERROR(WRITE_PROTECTION_VIOLATED)
      else if st.IsEipActive(3860) && codeSize > 2 * Code.MAX_CODE_SIZE then
        ERROR(INSUFFICIENT_GAS)
      else
        var code: seq<u8> := Memory.Slice(st.evm.memory, codeOffset, codeSize); var gascap: nat := GasCalc.CreateGasCap(st); var nst: ExecutingState := st.Expand(codeOffset, codeSize).Pop(4).Next(); if st.evm.world.Nonce(st.evm.context.address) < MAX_U64 then var nnst: ExecutingState := nst.UseGas(gascap).IncNonce(); CONTINUING(CREATES(nnst.evm, gascap, endowment, code, Some(salt))) else nst.Push(0)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function StaticCall(st: ExecutingState): (st': State)
    ensures st'.CONTINUING? || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.CONTINUING? <==> st.Operands() >= 6
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 6
    decreases st
  {
    if st.Operands() >= 6 then
      var outSize: nat := st.Peek(5) as nat;
      var outOffset: nat := st.Peek(4) as nat;
      var inSize: nat := st.Peek(3) as nat;
      var inOffset: nat := st.Peek(2) as nat;
      var to: u160 := (st.Peek(1) as int % TWO_160) as u160;
      var gas: nat := st.Peek(0) as nat;
      var gascap: nat := GasCalc.CallGasCap(st, gas);
      var callgas: nat := GasCalc.CallGas(st, gas, 0);
      var calldata: seq<u8> := Memory.Slice(st.evm.memory, inOffset, inSize);
      var address: u160 := st.evm.context.address;
      var nst: ExecutingState := st.AccountAccessed(to).UseGas(gascap).Expand(inOffset, inSize).Expand(outOffset, outSize).Pop(6).Next();
      CONTINUING(CALLS(nst.evm, address, to, to, callgas, 0, 0, calldata, false, outOffset := outOffset, outSize := outSize))
    else
      ERROR(STACK_UNDERFLOW)
  }

  function Revert(st: ExecutingState): (st': State)
    ensures st'.IsRevert() || st' == ERROR(STACK_UNDERFLOW)
    ensures st'.IsRevert() <==> st.Operands() >= 2
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 2
    decreases st
  {
    if st.Operands() >= 2 then
      var len: nat := st.Peek(1) as nat;
      var start: nat := st.Peek(0) as nat;
      var data: seq<u8> := Memory.Slice(st.evm.memory, start, len);
      ERROR(REVERTS, gas := st.evm.gas, data := data)
    else
      ERROR(STACK_UNDERFLOW)
  }

  function SelfDestruct(st: ExecutingState): (st': State)
    ensures st'.RETURNS? || st' == ERROR(STACK_UNDERFLOW) || st' == ERROR(WRITE_PROTECTION_VIOLATED)
    ensures st'.RETURNS? <==> st.Operands() >= 1 && st.WritesPermitted()
    ensures st'.RETURNS? ==> var a: u160 := st.evm.context.address; a in st'.world.accounts && st'.world.accounts[a] == st.evm.world.accounts[a].(balance := 0) && a in st'.substate.selfDestruct
    ensures st' == ERROR(STACK_UNDERFLOW) <==> st.Operands() < 1
    ensures st' == ERROR(WRITE_PROTECTION_VIOLATED) <==> st.Operands() >= 1 && !st.WritesPermitted()
    decreases st
  {
    if st.Operands() >= 1 then
      if !st.WritesPermitted() then
        ERROR(WRITE_PROTECTION_VIOLATED)
      else
        var address: u160 := st.evm.context.address; var balance: u256 := st.evm.world.Balance(address); var r: u160 := (st.Peek(0) as nat % TWO_160) as u160; var ss: Raw := st.evm.substate.AccountAccessed(r).AccountDestructed(address); var w: T := if address != r && (!st.Exists(r) || st.evm.world.CanDeposit(r, balance)) then st.evm.world.EnsureAccount(r).Transfer(address, r, balance) else st.evm.world.Withdraw(address, balance); RETURNS(gas := st.Gas(), data := [], world := w, transient := st.evm.transient, substate := ss)
    else
      ERROR(STACK_UNDERFLOW)
  }

  import opened Int

  import U256

  import I256

  import Word

  import ByteUtils

  import External

  import GasCalc = Gas

  import opened EvmState

  import opened Optional
}

module Gas {
  const G_ZERO: nat := 0
  const G_JUMPDEST: nat := 1
  const G_BASE: nat := 2
  const G_VERYLOW: nat := 3
  const G_LOW: nat := 5
  const G_MID: nat := 8
  const G_HIGH: nat := 10
  const G_WARMACCESS: nat := 100
  const G_COLDACCOUNTACCESS: nat := 2600
  const G_COLDSLOAD: nat := 2100
  const G_SSET: nat := 20000
  const G_SRESET: nat := 2900
  const R_SCLEAR: nat := 15000
  const R_SELFDESTRUCT: nat := 24000
  const G_SELFDESTRUCT: nat := 5000
  const G_CREATE: nat := 32000
  const G_CODEDEPOSIT: nat := 200
  const G_CALLVALUE: nat := 9000
  const G_CALLSTIPEND: nat := 2300
  const G_NEWACCOUNT: nat := 25000
  const G_EXP: nat := 10
  const G_EXPBYTE: nat := 50
  const G_MEMORY: nat := 3
  const G_TXCREATE: nat := 32000
  const G_TXDATAZERO: nat := 4
  const G_TXDATANONZERO: nat := 16
  const G_TRANSACTION: nat := 21000
  const G_LOG: nat := 375
  const G_LOGDATA: nat := 8
  const G_LOGTOPIC: nat := 375
  const G_KECCAK256: nat := 30
  const G_KECCAK256WORD: nat := 6
  const G_COPY: nat := 3
  const G_BLOCKHASH: nat := 20
  const G_ACCESS_LIST_ADDRESS_COST: nat := 2400
  const G_ACCESS_LIST_STORAGE_KEY_COST: nat := 1900
  const G_INITCODE_WORD_COST := 2

  function {:verify false} QuadraticCost(memUsedSize: nat): nat
    decreases memUsedSize
  {
    G_MEMORY * memUsedSize + memUsedSize * memUsedSize / 512
  }

  lemma {:verify false} QuadraticCostIsMonotonic(x: nat, y: nat)
    ensures x >= y ==> QuadraticCost(x) >= QuadraticCost(y)
    decreases x, y
  {
    if x > y {
      QuadraticCostIsMonotonic(x - 1, y);
    }
  }

  function ExpansionSize(mem: Memory.T, address: nat, len: nat): nat
    decreases mem, address, len
  {
    if len == 0 || address + len - 1 < |mem.contents| then
      0
    else
      var before: int := |mem.contents| / 32; var after: int := Memory.SmallestLarg32(address + len - 1) / 32; QuadraticCostIsMonotonic(after, before); assert QuadraticCost(after) >= QuadraticCost(before); QuadraticCost(after) - QuadraticCost(before)
  }

  function CostExpandBytes(st: ExecutingState, nOperands: nat, locSlot: nat, length: nat): nat
    requires nOperands > locSlot
    decreases st, nOperands, locSlot, length
  {
    if st.Operands() >= nOperands then
      var loc: nat := st.Peek(locSlot) as nat;
      ExpansionSize(st.evm.memory, loc, length)
    else
      G_ZERO
  }

  function CostExpandRange(st: ExecutingState, nOperands: nat, locSlot: nat, lenSlot: nat): nat
    requires nOperands > locSlot && nOperands > lenSlot
    decreases st, nOperands, locSlot, lenSlot
  {
    if st.Operands() >= nOperands then
      var loc: nat := st.Peek(locSlot) as nat;
      var len: nat := st.Peek(lenSlot) as nat;
      ExpansionSize(st.evm.memory, loc, len)
    else
      G_ZERO
  }

  function CostExpandDoubleRange(st: ExecutingState, nOperands: nat, aLocSlot: nat, aLenSlot: nat, bLocSlot: nat, bLenSlot: nat): nat
    requires nOperands > aLocSlot && nOperands > aLenSlot
    requires nOperands > bLocSlot && nOperands > bLenSlot
    decreases st, nOperands, aLocSlot, aLenSlot, bLocSlot, bLenSlot
  {
    if st.Operands() >= nOperands then
      var aCost: nat := CostExpandRange(st, nOperands, aLocSlot, aLenSlot);
      var bCost: nat := CostExpandRange(st, nOperands, bLocSlot, bLenSlot);
      Int.Max(aCost, bCost)
    else
      G_ZERO
  }

  function CostCopy(st: ExecutingState, lenSlot: nat): nat
    decreases st, lenSlot
  {
    if st.Operands() > lenSlot then
      var len: nat := st.Peek(lenSlot) as nat;
      var n: int := RoundUp(len, 32) / 32;
      G_COPY * n
    else
      G_ZERO
  }

  function CostInitCode(fork: Fork, len: nat): nat
    decreases fork, len
  {
    if fork.IsActive(3860) then
      G_INITCODE_WORD_COST * Int.RoundUp(len, 32) / 32
    else
      0
  }

  function CostCreate(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 3 then
      var len: nat := st.Peek(2) as nat;
      G_CREATE + CostInitCode(st.Fork(), len)
    else
      G_ZERO
  }

  function CostCreate2(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 4 then
      var len: nat := st.Peek(2) as nat;
      var rhs: int := RoundUp(len, 32) / 32;
      G_CREATE + G_KECCAK256WORD * rhs + CostInitCode(st.Fork(), len)
    else
      G_ZERO
  }

  function CostKeccak256(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 2 then
      var len: nat := st.Peek(1) as nat;
      var rhs: int := RoundUp(len, 32) / 32;
      G_KECCAK256 + G_KECCAK256WORD * rhs
    else
      G_ZERO
  }

  function CostLog(st: ExecutingState, n: nat): nat
    decreases st, n
  {
    if st.Operands() >= 2 then
      var loc: nat := st.Peek(0) as nat;
      var len: nat := st.Peek(1) as nat;
      G_LOG + len * G_LOGDATA + n * G_LOGTOPIC
    else
      G_ZERO
  }

  function CallCost(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 7 then
      var value: nat := st.Peek(2) as nat;
      var to: u160 := (st.Peek(1) as int % TWO_160) as u160;
      CostAccess(st, to) + CostCallXfer(value) + CostCallNew(st, to, value)
    else
      G_ZERO
  }

  function CallCodeCost(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 7 then
      var value: nat := st.Peek(2) as nat;
      var to: u160 := (st.Peek(1) as int % TWO_160) as u160;
      CostAccess(st, to) + CostCallXfer(value)
    else
      G_ZERO
  }

  function DelegateCallCost(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 6 then
      var to: u160 := (st.Peek(1) as int % TWO_160) as u160;
      CostAccess(st, to)
    else
      G_ZERO
  }

  function StaticCallCost(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 6 then
      var to: u160 := (st.Peek(1) as int % TWO_160) as u160;
      CostAccess(st, to)
    else
      G_ZERO
  }

  function CallGas(st: ExecutingState, gas: nat, value: u256): (r: nat)
    decreases st, gas, value
  {
    CallGasCap(st, gas) + CallStipend(value)
  }

  function CallStipend(value: u256): (r: nat)
    decreases value
  {
    if value != 0 then
      G_CALLSTIPEND
    else
      0
  }

  function CallGasCap(st: ExecutingState, gas: nat): (r: nat)
    decreases st, gas
  {
    Min(L(st.Gas()), gas)
  }

  function CreateGasCap(st: ExecutingState): (r: nat)
    decreases st
  {
    L(st.Gas())
  }

  function L(n: nat): nat
    decreases n
  {
    n - n / 64
  }

  function CostCallExtra(st: ExecutingState, to: u160, value: nat): nat
    decreases st, to, value
  {
    CostAccess(st, to) + CostCallXfer(value) + CostCallNew(st, to, value)
  }

  function CostCallXfer(value: nat): nat
    decreases value
  {
    if value != 0 then
      G_CALLVALUE
    else
      0
  }

  function CostCallNew(st: ExecutingState, to: u160, value: nat): nat
    decreases st, to, value
  {
    if st.IsDead(to) && value != 0 then
      G_NEWACCOUNT
    else
      0
  }

  function CostExtAccount(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 1 then
      var account: u160 := (st.Peek(0) as nat % TWO_160) as u160;
      CostAccess(st, account)
    else
      G_ZERO
  }

  function CostAccess(st: ExecutingState, x: u160): nat
    decreases st, x
  {
    if st.WasAccountAccessed(x) then
      G_WARMACCESS
    else
      G_COLDACCOUNTACCESS
  }

  function CostSLoad(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 1 then
      var loc: u256 := st.Peek(0);
      if st.WasKeyAccessed(loc) then
        G_WARMACCESS
      else
        G_COLDSLOAD
    else
      G_ZERO
  }

  function CostSStore(st: ExecutingState): nat
    decreases st
  {
    var currentAccount: Account := st.evm.world.GetAccount(st.evm.context.address).Unwrap();
    var originalAccount: Account := st.evm.world.GetOrDefaultPretransaction(st.evm.context.address);
    if st.Gas() <= G_CALLSTIPEND then
      MAX_U256
    else if st.Operands() >= 2 then
      var loc: u256 := st.Peek(0);
      var newVal: nat := st.Peek(1) as nat;
      var accessCost: int := if st.WasKeyAccessed(loc) then 0 else G_COLDSLOAD;
      var currentVal: nat := Storage.Read(currentAccount.storage, loc) as nat;
      var originalVal: nat := Storage.Read(originalAccount.storage, loc) as nat;
      CostSStoreCalc(originalVal, currentVal, newVal) + accessCost
    else
      G_ZERO
  }

  function CostSStoreCalc(originalVal: nat, currentVal: nat, newVal: nat): nat
    decreases originalVal, currentVal, newVal
  {
    if currentVal == newVal then
      G_WARMACCESS
    else if originalVal == currentVal then
      if originalVal == 0 then
        G_SSET
      else
        G_SRESET
    else
      G_WARMACCESS
  }

  function CostSelfDestruct(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 1 then
      var r: u160 := (st.Peek(0) as nat % TWO_160) as u160;
      G_SELFDESTRUCT + CostSelfDestructAccess(st, r) + CostSelfDestructNewAccount(st, r)
    else
      G_ZERO
  }

  function CostSelfDestructAccess(st: ExecutingState, r: u160): nat
    decreases st, r
  {
    if st.WasAccountAccessed(r) then
      0
    else
      G_COLDACCOUNTACCESS
  }

  function CostSelfDestructNewAccount(st: ExecutingState, r: u160): nat
    decreases st, r
  {
    var Ia: u160 := st.evm.context.address;
    if st.evm.world.IsDead(r) && st.evm.world.Balance(Ia) != 0 then
      G_NEWACCOUNT
    else
      0
  }

  function CostExp(st: ExecutingState): nat
    decreases st
  {
    if st.Operands() >= 2 then
      var exp: u256 := st.Peek(1);
      if exp == 0 then
        G_EXP
      else
        var l256: int := 1 + U256.Log256(exp); G_EXP + G_EXPBYTE * l256
    else
      G_ZERO
  }

  import opened Opcode

  import opened EvmState

  import opened EvmFork

  import opened Int

  import opened Memory
}

module ByteUtils {
  function ReadUint8(mem: seq<u8>, address: nat): u8
    decreases mem, address
  {
    if address < |mem| then
      mem[address]
    else
      0
  }

  function ReadUint16(mem: seq<u8>, address: nat): u16
    decreases mem, address
  {
    var w1: u16 := ReadUint8(mem, address) as u16;
    var w2: u16 := ReadUint8(mem, address + 1) as u16;
    w1 * TWO_8 as u16 + w2
  }

  function ReadUint32(mem: seq<u8>, address: nat): u32
    decreases mem, address
  {
    var w1: u32 := ReadUint16(mem, address) as u32;
    var w2: u32 := ReadUint16(mem, address + 2) as u32;
    w1 * TWO_16 as u32 + w2
  }

  function ReadUint64(mem: seq<u8>, address: nat): u64
    decreases mem, address
  {
    var w1: u64 := ReadUint32(mem, address) as u64;
    var w2: u64 := ReadUint32(mem, address + 4) as u64;
    w1 * TWO_32 as u64 + w2
  }

  function ReadUint128(mem: seq<u8>, address: nat): u128
    decreases mem, address
  {
    var w1: u128 := ReadUint64(mem, address) as u128;
    var w2: u128 := ReadUint64(mem, address + 8) as u128;
    w1 * TWO_64 as u128 + w2
  }

  function ReadUint256(mem: seq<u8>, address: nat): u256
    decreases mem, address
  {
    var w1: u256 := ReadUint128(mem, address) as u256;
    var w2: u256 := ReadUint128(mem, address + 16) as u256;
    w1 * TWO_128 as u256 + w2
  }

  function WriteUint8(mem: seq<u8>, address: nat, val: u8): (mem': seq<u8>)
    requires address < |mem|
    ensures Arrays.EqualsExcept(mem, mem', address, 1)
    decreases mem, address, val
  {
    mem[address := val]
  }

  function WriteUint16(mem: seq<u8>, address: nat, val: u16): (mem': seq<u8>)
    requires address + 1 < |mem|
    ensures Arrays.EqualsExcept(mem, mem', address, 2)
    decreases mem, address, val
  {
    var w1: u16 := val / TWO_8 as u16;
    var w2: u16 := val % TWO_8 as u16;
    var mem': seq<u8> := WriteUint8(mem, address, w1 as u8);
    WriteUint8(mem', address + 1, w2 as u8)
  }

  function WriteUint32(mem: seq<u8>, address: nat, val: u32): (mem': seq<u8>)
    requires address + 3 < |mem|
    ensures Arrays.EqualsExcept(mem, mem', address, 4)
    decreases mem, address, val
  {
    var w1: u32 := val / TWO_16 as u32;
    var w2: u32 := val % TWO_16 as u32;
    var mem': seq<u8> := WriteUint16(mem, address, w1 as u16);
    WriteUint16(mem', address + 2, w2 as u16)
  }

  function WriteUint64(mem: seq<u8>, address: nat, val: u64): (mem': seq<u8>)
    requires address + 7 < |mem|
    ensures Arrays.EqualsExcept(mem, mem', address, 8)
    decreases mem, address, val
  {
    var w1: u64 := val / TWO_32 as u64;
    var w2: u64 := val % TWO_32 as u64;
    var mem': seq<u8> := WriteUint32(mem, address, w1 as u32);
    WriteUint32(mem', address + 4, w2 as u32)
  }

  function WriteUint128(mem: seq<u8>, address: nat, val: u128): (mem': seq<u8>)
    requires address + 15 < |mem|
    ensures Arrays.EqualsExcept(mem, mem', address, 16)
    decreases mem, address, val
  {
    var w1: u128 := val / TWO_64 as u128;
    var w2: u128 := val % TWO_64 as u128;
    var mem': seq<u8> := WriteUint64(mem, address, w1 as u64);
    WriteUint64(mem', address + 8, w2 as u64)
  }

  function WriteUint256(mem: seq<u8>, address: nat, val: u256): (mem': seq<u8>)
    requires address + 31 < |mem|
    ensures Arrays.EqualsExcept(mem, mem', address, 32)
    decreases mem, address, val
  {
    var w1: u256 := val / TWO_128 as u256;
    var w2: u256 := val % TWO_128 as u256;
    var mem': seq<u8> := WriteUint128(mem, address, w1 as u128);
    WriteUint128(mem', address + 16, w2 as u128)
  }

  function ConvertBytesTo256(bytes: seq<u8>): u256
    requires 0 < |bytes| <= 32
    decreases bytes
  {
    if |bytes| == 1 then
      bytes[0] as u256
    else if |bytes| == 2 then
      ReadUint16(bytes, 0) as u256
    else if |bytes| <= 4 then
      ReadUint32(LeftPad(bytes, 4), 0) as u256
    else if |bytes| <= 8 then
      ReadUint64(LeftPad(bytes, 8), 0) as u256
    else if |bytes| <= 16 then
      ReadUint128(LeftPad(bytes, 16), 0) as u256
    else
      ReadUint256(LeftPad(bytes, 32), 0)
  }

  function LeftPad(bytes: seq<u8>, n: nat): seq<u8>
    requires |bytes| <= n
    decreases bytes, n
  {
    var k: int := n - |bytes|;
    Padding(k) + bytes
  }

  function Padding(n: nat): seq<u8>
    ensures |Padding(n)| == n
    decreases n
  {
    seq(n, (i: int) => 0)
  }

  import opened Int

  import Arrays
}

module Arrays {
  predicate EqualsExcept<T(==)>(lhs: seq<T>, rhs: seq<T>, address: nat, length: nat)
    requires address + length <= |lhs|
    decreases lhs, rhs, address, length
  {
    |lhs| == |rhs| &&
    lhs[..address] == rhs[..address] &&
    lhs[address + length..] == rhs[address + length..]
  }

  function SliceAndPad<T>(mem: seq<T>, address: nat, len: nat, padding: T): (result: seq<T>)
    ensures |result| == len
    decreases mem, address, len
  {
    var n: int := address + len;
    if n <= |mem| then
      mem[address .. n]
    else if address < |mem| then
      mem[address..] + seq(n - |mem|, (i: int) => padding)
    else
      seq(len, (i: int) => padding)
  }

  opaque function Copy<T>(src: seq<T>, dst: seq<T>, start: nat): (result: seq<T>)
    requires start + |src| <= |dst|
    ensures |result| == |dst|
    ensures src == result[start .. start + |src|]
    ensures EqualsExcept(dst, result, start, |src|)
    decreases src, dst, start
  {
    var end: int := start + |src|;
    seq(|dst|, (i: int) requires i >= 0 && i < |dst| => if i >= start && i < end then src[i - start] else dst[i])
  }

  import opened Int

  type Array<T> = arr: seq<T>
    | |arr| < TWO_256
}

module Int {
  const TWO_1: int := 2
  const TWO_2: int := 4
  const TWO_3: int := 8
  const TWO_4: int := 16
  const TWO_5: int := 32
  const TWO_6: int := 64
  const TWO_7: int := 128
  const TWO_8: int := 256
  const TWO_15: int := 32768
  const TWO_16: int := 65536
  const TWO_24: int := 16777216
  const TWO_31: int := 2147483648
  const TWO_32: int := 4294967296
  const TWO_40: int := 1099511627776
  const TWO_48: int := 281474976710656
  const TWO_56: int := 72057594037927936
  const TWO_63: int := 9223372036854775808
  const TWO_64: int := 18446744073709551616
  const TWO_72: int := 4722366482869645213696
  const TWO_80: int := 1208925819614629174706176
  const TWO_88: int := 309485009821345068724781056
  const TWO_96: int := 79228162514264337593543950336
  const TWO_104: int := 20282409603651670423947251286016
  const TWO_112: int := 5192296858534827628530496329220096
  const TWO_120: int := 1329227995784915872903807060280344576
  const TWO_127: int := 170141183460469231731687303715884105728
  const TWO_128: int := 340282366920938463463374607431768211456
  const TWO_136: int := 87112285931760246646623899502532662132736
  const TWO_144: int := 22300745198530623141535718272648361505980416
  const TWO_152: int := 5708990770823839524233143877797980545530986496
  const TWO_160: int := 1461501637330902918203684832716283019655932542976
  const TWO_168: int := 374144419156711147060143317175368453031918731001856
  const TWO_176: int := 95780971304118053647396689196894323976171195136475136
  const TWO_184: int := 24519928653854221733733552434404946937899825954937634816
  const TWO_192: int := 6277101735386680763835789423207666416102355444464034512896
  const TWO_200: int := 1606938044258990275541962092341162602522202993782792835301376
  const TWO_208: int := 411376139330301510538742295639337626245683966408394965837152256
  const TWO_216: int := 105312291668557186697918027683670432318895095400549111254310977536
  const TWO_224: int := 26959946667150639794667015087019630673637144422540572481103610249216
  const TWO_232: int := 6901746346790563787434755862277025452451108972170386555162524223799296
  const TWO_240: int := 1766847064778384329583297500742918515827483896875618958121606201292619776
  const TWO_248: int := 452312848583266388373324160190187140051835877600158453279131187530910662656
  const TWO_255: int := 57896044618658097711785492504343953926634992332820282019728792003956564819968
  const TWO_256: int := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  const MIN_I8: int := -TWO_7
  const MAX_I8: int := TWO_7 - 1
  const MIN_I16: int := -TWO_15
  const MAX_I16: int := TWO_15 - 1
  const MIN_I32: int := -TWO_31
  const MAX_I32: int := TWO_31 - 1
  const MIN_I64: int := -TWO_63
  const MAX_I64: int := TWO_63 - 1
  const MIN_I128: int := -TWO_127
  const MAX_I128: int := TWO_127 - 1
  const MIN_I256: int := -TWO_255
  const MAX_I256: int := TWO_255 - 1
  const MAX_U1: int := TWO_1 - 1
  const MAX_U2: int := TWO_2 - 1
  const MAX_U3: int := TWO_3 - 1
  const MAX_U4: int := TWO_4 - 1
  const MAX_U5: int := TWO_5 - 1
  const MAX_U6: int := TWO_6 - 1
  const MAX_U7: int := TWO_7 - 1
  const MAX_U8: int := TWO_8 - 1
  const MAX_U16: int := TWO_16 - 1
  const MAX_U24: int := TWO_24 - 1
  const MAX_U32: int := TWO_32 - 1
  const MAX_U40: int := TWO_40 - 1
  const MAX_U48: int := TWO_48 - 1
  const MAX_U56: int := TWO_56 - 1
  const MAX_U64: int := TWO_64 - 1
  const MAX_U72: int := TWO_72 - 1
  const MAX_U80: int := TWO_80 - 1
  const MAX_U88: int := TWO_88 - 1
  const MAX_U96: int := TWO_96 - 1
  const MAX_U104: int := TWO_104 - 1
  const MAX_U112: int := TWO_112 - 1
  const MAX_U120: int := TWO_120 - 1
  const MAX_U128: int := TWO_128 - 1
  const MAX_U136: int := TWO_136 - 1
  const MAX_U144: int := TWO_144 - 1
  const MAX_U152: int := TWO_152 - 1
  const MAX_U160: int := TWO_160 - 1
  const MAX_U168: int := TWO_168 - 1
  const MAX_U176: int := TWO_176 - 1
  const MAX_U184: int := TWO_184 - 1
  const MAX_U192: int := TWO_192 - 1
  const MAX_U200: int := TWO_200 - 1
  const MAX_U208: int := TWO_208 - 1
  const MAX_U216: int := TWO_216 - 1
  const MAX_U224: int := TWO_224 - 1
  const MAX_U232: int := TWO_232 - 1
  const MAX_U240: int := TWO_240 - 1
  const MAX_U248: int := TWO_248 - 1
  const MAX_U256: int := TWO_256 - 1

  function Abs(x: int): nat
    decreases x
  {
    if x >= 0 then
      x
    else
      -x
  }

  function Max(i1: int, i2: int): int
    decreases i1, i2
  {
    if i1 >= i2 then
      i1
    else
      i2
  }

  function Min(i1: int, i2: int): int
    decreases i1, i2
  {
    if i1 < i2 then
      i1
    else
      i2
  }

  function RoundUp(i: int, r: nat): int
    requires r > 0
    decreases i, r
  {
    if i % r == 0 then
      i
    else
      i / r * r + r
  }

  function MaxUnsignedN(n: nat): (r: nat)
    requires 1 <= n <= 32
    decreases n
  {
    match n
    case 1 =>
      MAX_U8
    case 2 =>
      MAX_U16
    case 3 =>
      MAX_U24
    case 4 =>
      MAX_U32
    case 5 =>
      MAX_U40
    case 6 =>
      MAX_U48
    case 7 =>
      MAX_U56
    case 8 =>
      MAX_U64
    case 9 =>
      MAX_U72
    case 10 =>
      MAX_U80
    case 11 =>
      MAX_U88
    case 12 =>
      MAX_U96
    case 13 =>
      MAX_U104
    case 14 =>
      MAX_U112
    case 15 =>
      MAX_U120
    case 16 =>
      MAX_U128
    case 17 =>
      MAX_U136
    case 18 =>
      MAX_U144
    case 19 =>
      MAX_U152
    case 20 =>
      MAX_U160
    case 21 =>
      MAX_U168
    case 22 =>
      MAX_U176
    case 23 =>
      MAX_U184
    case 24 =>
      MAX_U192
    case 25 =>
      MAX_U200
    case 26 =>
      MAX_U208
    case 27 =>
      MAX_U216
    case 28 =>
      MAX_U224
    case 29 =>
      MAX_U232
    case 30 =>
      MAX_U240
    case 31 =>
      MAX_U248
    case 32 =>
      MAX_U256
    case _ /* _v0 */ =>
      MathUtils.Pow(2, n) - 1
  }

  function Div(lhs: int, rhs: int): int
    requires rhs != 0
    decreases lhs, rhs
  {
    if lhs >= 0 then
      lhs / rhs
    else
      -(-lhs / rhs)
  }

  function Rem(lhs: int, rhs: int): int
    requires rhs != 0
    decreases lhs, rhs
  {
    if lhs >= 0 then
      lhs % rhs
    else
      var d: int := -(-lhs / rhs); lhs - d * rhs
  }

  function {:tailrecursion true} ToBytes(v: nat): (r: seq<u8>)
    ensures |r| > 0
    decreases v
  {
    var byte: u8 := (v % 256) as u8;
    var w: nat := v / 256;
    if w == 0 then
      [byte]
    else
      ToBytes(w) + [byte]
  }

  function FromBytes(bytes: seq<u8>): (r: nat)
    decreases bytes
  {
    if |bytes| == 0 then
      0
    else
      var last: int := |bytes| - 1; var byte: nat := bytes[last] as nat; var msw: nat := FromBytes(bytes[..last]); msw * 256 + byte
  } by method {
    r := 0;
    for i: int := 0 to |bytes|
      invariant r == FromBytes(bytes[..i])
    {
      var ith := bytes[i] as nat;
      r := r * 256 + ith;
      LemmaFromBytes(bytes, i);
    }
    assert bytes[..|bytes|] == bytes;
    return r;
  }

  lemma LemmaFromBytes(bytes: seq<u8>, i: nat)
    requires 0 <= i < |bytes|
    ensures FromBytes(bytes[..i + 1]) == FromBytes(bytes[..i]) * 256 + bytes[i] as nat
    decreases bytes, i
  {
    if i != 0 {
      ghost var cons := bytes[..i + 1];
      ghost var tail := bytes[..i];
      ghost var head := bytes[i];
      assert cons == tail + [head];
    }
  }

  lemma /*{:_inductionTrigger ToBytes(v)}*/ /*{:_induction v}*/ LemmaFromToBytes(v: nat)
    ensures FromBytes(ToBytes(v)) == v
    decreases v
  {
  }

  lemma {:verify false} /*{:_inductionTrigger FromBytes(bytes)}*/ /*{:_inductionTrigger bytes[0]}*/ /*{:_inductionTrigger |bytes|}*/ /*{:_induction bytes}*/ LemmaToFromBytes(bytes: seq<u8>)
    requires |bytes| > 0 && (|bytes| == 1 || bytes[0] != 0)
    ensures ToBytes(FromBytes(bytes)) == bytes
    decreases bytes
  {
    ghost var n := |bytes| - 1;
    if |bytes| > 1 {
      ghost var tail := bytes[..n];
      LemmaToFromBytes(tail);
    } else {
      assert ToBytes(FromBytes(bytes)) == bytes;
    }
  }

  lemma /*{:_inductionTrigger ToBytes(m), ToBytes(n)}*/ /*{:_induction n, m}*/ LemmaLengthToBytes(n: nat, m: nat)
    requires n <= m
    ensures |ToBytes(n)| <= |ToBytes(m)|
    decreases n, m
  {
  }

  lemma /*{:_inductionTrigger |bytes|, |ToBytes(n)|}*/ /*{:_inductionTrigger ToBytes(n), FromBytes(bytes)}*/ /*{:_induction n, bytes}*/ LemmaLengthFromBytes(n: nat, bytes: seq<u8>)
    requires n == FromBytes(bytes)
    ensures bytes == [] || |ToBytes(n)| <= |bytes|
    decreases n, bytes
  {
    if |bytes| == 1 {
      assert |ToBytes(n)| == 1;
    } else if |bytes| > 1 {
      ghost var last := |bytes| - 1;
      ghost var tail := bytes[..last];
      LemmaLengthFromBytes(n / 256, tail);
    }
  }

  import opened Optional

  import MathUtils

  newtype {:nativeType "sbyte"} i8 = i: int
    | MIN_I8 <= i <= MAX_I8

  newtype {:nativeType "short"} i16 = i: int
    | MIN_I16 <= i <= MAX_I16

  newtype {:nativeType "int"} i32 = i: int
    | MIN_I32 <= i <= MAX_I32

  newtype {:nativeType "long"} i64 = i: int
    | MIN_I64 <= i <= MAX_I64

  newtype i128 = i: int
    | MIN_I128 <= i <= MAX_I128

  newtype i256 = i: int
    | MIN_I256 <= i <= MAX_I256

  newtype {:nativeType "byte"} u1 = i: int
    | 0 <= i <= MAX_U1

  newtype {:nativeType "byte"} u2 = i: int
    | 0 <= i <= MAX_U2

  newtype {:nativeType "byte"} u3 = i: int
    | 0 <= i <= MAX_U3

  newtype {:nativeType "byte"} u4 = i: int
    | 0 <= i <= MAX_U4

  newtype {:nativeType "byte"} u5 = i: int
    | 0 <= i <= MAX_U5

  newtype {:nativeType "byte"} u6 = i: int
    | 0 <= i <= MAX_U6

  newtype {:nativeType "byte"} u7 = i: int
    | 0 <= i <= MAX_U7

  newtype {:nativeType "byte"} u8 = i: int
    | 0 <= i <= MAX_U8

  newtype {:nativeType "ushort"} u16 = i: int
    | 0 <= i <= MAX_U16

  newtype {:nativeType "uint"} u24 = i: int
    | 0 <= i <= MAX_U24

  newtype {:nativeType "uint"} u32 = i: int
    | 0 <= i <= MAX_U32

  newtype {:nativeType "ulong"} u40 = i: int
    | 0 <= i <= MAX_U40

  newtype {:nativeType "ulong"} u48 = i: int
    | 0 <= i <= MAX_U48

  newtype {:nativeType "ulong"} u56 = i: int
    | 0 <= i <= MAX_U56

  newtype {:nativeType "ulong"} u64 = i: int
    | 0 <= i <= MAX_U64

  newtype u128 = i: int
    | 0 <= i <= MAX_U128

  newtype u160 = i: int
    | 0 <= i <= MAX_U160

  newtype u256 = i: int
    | 0 <= i <= MAX_U256
}

module U8 {
  function Log2(v: u8): (r: nat)
    ensures r < 8
    decreases v
  {
    if v <= 15 then
      if v <= 3 then
        if v <= 1 then
          0
        else
          1
      else if v <= 7 then
        2
      else
        3
    else if v <= 63 then
      if v <= 31 then
        4
      else
        5
    else if v <= 127 then
      6
    else
      7
  }

  import opened Int
}

module U16 {
  function NthUint8(v: u16, k: nat): u8
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_8 as u16) as u8
    else
      (v % TWO_8 as u16) as u8
  }

  function Log2(v: u16): (r: nat)
    ensures r < 16
    decreases v
  {
    var low: u8 := (v % TWO_8 as u16) as u8;
    var high: u8 := (v / TWO_8 as u16) as u8;
    if high != 0 then
      U8.Log2(high) + 8
    else
      U8.Log2(low)
  }

  function Log256(v: u16): (r: nat)
    ensures r <= 1
    decreases v
  {
    var low: u8 := (v % TWO_8 as u16) as u8;
    var high: u8 := (v / TWO_8 as u16) as u8;
    if high != 0 then
      1
    else
      0
  }

  function ToBytes(v: u16): (r: seq<u8>)
    ensures |r| == 2
    decreases v
  {
    var low: u8 := (v % TWO_8 as u16) as u8;
    var high: u8 := (v / TWO_8 as u16) as u8;
    [high, low]
  }

  function Read(bytes: seq<u8>, address: nat): u16
    requires address + 1 < |bytes|
    decreases bytes, address
  {
    var b1: u16 := bytes[address] as u16;
    var b2: u16 := bytes[address + 1] as u16;
    b1 * TWO_8 as u16 + b2
  }

  import opened Int

  import U8
}

module U32 {
  function NthUint16(v: u32, k: nat): u16
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_16 as u32) as u16
    else
      (v % TWO_16 as u32) as u16
  }

  function Log2(v: u32): (r: nat)
    ensures r < 32
    decreases v
  {
    var low: u16 := (v % TWO_16 as u32) as u16;
    var high: u16 := (v / TWO_16 as u32) as u16;
    if high != 0 then
      U16.Log2(high) + 16
    else
      U16.Log2(low)
  }

  function Log256(v: u32): (r: nat)
    ensures r <= 3
    decreases v
  {
    var low: u16 := (v % TWO_16 as u32) as u16;
    var high: u16 := (v / TWO_16 as u32) as u16;
    if high != 0 then
      U16.Log256(high) + 2
    else
      U16.Log256(low)
  }

  function ToBytes(v: u32): (r: seq<u8>)
    ensures |r| == 4
    decreases v
  {
    var low: u16 := (v % TWO_16 as u32) as u16;
    var high: u16 := (v / TWO_16 as u32) as u16;
    U16.ToBytes(high) + U16.ToBytes(low)
  }

  function Read(bytes: seq<u8>, address: nat): u32
    requires address + 3 < |bytes|
    decreases bytes, address
  {
    var b1: u32 := U16.Read(bytes, address) as u32;
    var b2: u32 := U16.Read(bytes, address + 2) as u32;
    b1 * TWO_16 as u32 + b2
  }

  import U16

  import opened Int
}

module U64 {
  function NthUint32(v: u64, k: nat): u32
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_32 as u64) as u32
    else
      (v % TWO_32 as u64) as u32
  }

  function Log2(v: u64): (r: nat)
    ensures r < 64
    decreases v
  {
    var low: u32 := (v % TWO_32 as u64) as u32;
    var high: u32 := (v / TWO_32 as u64) as u32;
    if high != 0 then
      U32.Log2(high) + 32
    else
      U32.Log2(low)
  }

  function Log256(v: u64): (r: nat)
    ensures r <= 7
    decreases v
  {
    var low: u32 := (v % TWO_32 as u64) as u32;
    var high: u32 := (v / TWO_32 as u64) as u32;
    if high != 0 then
      U32.Log256(high) + 4
    else
      U32.Log256(low)
  }

  function ToBytes(v: u64): (r: seq<u8>)
    ensures |r| == 8
    decreases v
  {
    var low: u32 := (v % TWO_32 as u64) as u32;
    var high: u32 := (v / TWO_32 as u64) as u32;
    U32.ToBytes(high) + U32.ToBytes(low)
  }

  function Read(bytes: seq<u8>, address: nat): u64
    requires address + 7 < |bytes|
    decreases bytes, address
  {
    var b1: u64 := U32.Read(bytes, address) as u64;
    var b2: u64 := U32.Read(bytes, address + 4) as u64;
    b1 * TWO_32 as u64 + b2
  }

  import U32

  import opened Int
}

module U128 {
  function NthUint64(v: u128, k: nat): u64
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_64 as u128) as u64
    else
      (v % TWO_64 as u128) as u64
  }

  function Log2(v: u128): (r: nat)
    ensures r < 128
    decreases v
  {
    var low: u64 := (v % TWO_64 as u128) as u64;
    var high: u64 := (v / TWO_64 as u128) as u64;
    if high != 0 then
      U64.Log2(high) + 64
    else
      U64.Log2(low)
  }

  function Log256(v: u128): (r: nat)
    ensures r <= 15
    decreases v
  {
    var low: u64 := (v % TWO_64 as u128) as u64;
    var high: u64 := (v / TWO_64 as u128) as u64;
    if high != 0 then
      U64.Log256(high) + 8
    else
      U64.Log256(low)
  }

  function ToBytes(v: u128): (r: seq<u8>)
    ensures |r| == 16
    decreases v
  {
    var low: u64 := (v % TWO_64 as u128) as u64;
    var high: u64 := (v / TWO_64 as u128) as u64;
    U64.ToBytes(high) + U64.ToBytes(low)
  }

  function Read(bytes: seq<u8>, address: nat): u128
    requires address + 15 < |bytes|
    decreases bytes, address
  {
    var b1: u128 := U64.Read(bytes, address) as u128;
    var b2: u128 := U64.Read(bytes, address + 8) as u128;
    b1 * TWO_64 as u128 + b2
  }

  import U64

  import opened Int
}

module U256 {
  lemma {:axiom} as_bv256_as_u256(v: bv256)
    ensures v as nat < TWO_256
    decreases v

  function Shl(lhs: u256, rhs: u256): u256
    decreases lhs, rhs
  {
    if rhs >= 256 then
      0
    else
      var p: nat := MathUtils.Pow(2, rhs as nat); var n: int := lhs as nat * p; (n % TWO_256) as u256
  }

  function Shr(lhs: u256, rhs: u256): u256
    decreases lhs, rhs
  {
    if rhs >= 256 then
      0
    else
      var p: nat := MathUtils.Pow(2, rhs as nat); var n: int := lhs as nat / p; n as u256
  }

  function Log2(v: u256): (r: nat)
    ensures r < 256
    decreases v
  {
    var low: u128 := (v % TWO_128 as u256) as u128;
    var high: u128 := (v / TWO_128 as u256) as u128;
    if high != 0 then
      U128.Log2(high) + 128
    else
      U128.Log2(low)
  }

  function Log256(v: u256): (r: nat)
    ensures r <= 31
    decreases v
  {
    var low: u128 := (v % TWO_128 as u256) as u128;
    var high: u128 := (v / TWO_128 as u256) as u128;
    if high != 0 then
      U128.Log256(high) + 16
    else
      U128.Log256(low)
  }

  function NthUint128(v: u256, k: nat): u128
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_128 as u256) as u128
    else
      (v % TWO_128 as u256) as u128
  }

  function NthUint8(v: u256, k: nat): u8
    requires k < 32
    decreases v, k
  {
    var w128: u128 := NthUint128(v, k / 16);
    var w64: u64 := U128.NthUint64(w128, k % 16 / 8);
    var w32: u32 := U64.NthUint32(w64, k % 8 / 4);
    var w16: u16 := U32.NthUint16(w32, k % 4 / 2);
    U16.NthUint8(w16, k % 2)
  }

  function Read(bytes: seq<u8>, address: nat): u256
    requires address + 31 < |bytes|
    decreases bytes, address
  {
    var b1: u256 := U128.Read(bytes, address) as u256;
    var b2: u256 := U128.Read(bytes, address + 16) as u256;
    b1 * TWO_128 as u256 + b2
  }

  function ToBytes(v: u256): (r: seq<u8>)
    ensures |r| == 32
    decreases v
  {
    var low: u128 := (v % TWO_128 as u256) as u128;
    var high: u128 := (v / TWO_128 as u256) as u128;
    U128.ToBytes(high) + U128.ToBytes(low)
  }

  function SignExtend(v: u256, k: nat): u256
    decreases v, k
  {
    if k >= 31 then
      v
    else
      var ith: int := 31 - k; var byte: u8 := NthUint8(v, ith); var signs: seq<u8> := if byte >= 128 then seq(31 - k, (i: int) => 255) else seq(31 - k, (i: int) => 0); var bytes: seq<u8> := ToBytes(v)[ith..]; assert |signs + bytes| == 32; Read(signs + bytes, 0)
  }

  import opened Int

  import U8

  import U16

  import U32

  import U64

  import U128
}

module I256 {
  function Div(lhs: i256, rhs: i256): i256
    requires rhs != 0
    requires rhs != -1 || lhs != -TWO_255 as i256
    decreases lhs, rhs
  {
    Int.Div(lhs as int, rhs as int) as i256
  }

  function Rem(lhs: i256, rhs: i256): i256
    requires rhs != 0
    decreases lhs, rhs
  {
    Int.Rem(lhs as int, rhs as int) as i256
  }

  function Sar(lhs: i256, rhs: u256): i256
    decreases lhs, rhs
  {
    if rhs == 0 then
      lhs
    else if rhs < 256 then
      assert 0 < rhs < 256;
      var r: nat := MathUtils.Pow(2, rhs as nat);
      (lhs as int / r as int) as i256
    else if lhs < 0 then
      -1
    else
      0
  }

  import U256

  import Word

  import opened Int
}

module Word {
  function asI256(w: u256): i256
    decreases w
  {
    if w > MAX_I256 as u256 then
      var v: int := 1 + MAX_U256 - w as int;
      -v as i256
    else
      w as i256
  }

  function fromI256(w: Int.i256): u256
    decreases w
  {
    if w < 0 then
      var v: int := 1 + MAX_U256 + w as int;
      v as u256
    else
      w as u256
  }

  import opened Int
}

module Optional {
  datatype Option<T> = Some(v: T) | None {
    function Unwrap(): T
      requires this.Some?
      decreases this
    {
      this.v
    }

    function UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case none =>
        default
    }
  }
}

module MathUtils {
  function Abs(x: int): nat
    decreases x
  {
    if x >= 0 then
      x
    else
      -x
  }

  function Pow(n: nat, k: nat): (r: nat)
    ensures n > 0 ==> r > 0
    decreases n, k
  {
    if k == 0 then
      1
    else if k == 1 then
      n
    else
      var p: int := k / 2; var np: nat := Pow(n, p); if p * 2 == k then np * np else np * np * n
  }

  lemma /*{:_inductionTrigger Pow(2, k)}*/ /*{:_induction k}*/ lemma_pow2(k: nat)
    ensures Pow(2, k) > 0
    decreases k
  {
    if k == 0 {
      assert Pow(2, k) == 1;
    } else if k == 1 {
      assert Pow(2, k) == 2;
    } else {
      lemma_pow2(k / 2);
    }
  }

  function ModPow(n: nat, k: nat, m: nat): (r: nat)
    requires m > 0
    ensures r < m
    ensures n > 0 ==> r >= 0
    decreases k
  {
    var nm: int := n % m;
    if k == 0 || m == 1 then
      1 % m
    else if k == 1 then
      nm
    else
      var np: nat := ModPow(nm, k / 2, m); var np2: int := np * np % m; if k % 2 == 0 then np2 else np2 * nm % m
  }

  function GcdExtended(a: nat, b: nat): (r: (nat, int, int))
    ensures b > 0 ==> r.0 > 0
    ensures a * r.1 + b * r.2 == r.0
    decreases a, b
  {
    if a == 0 then
      (b, 0, 1)
    else
      var (g: nat, x: int, y: int) := GcdExtended(b % a, a); (g, y - b / a * x, x)
  }

  function Inverse(a: nat, n: nat): (r: Option<nat>)
    requires a < n
    ensures r != None ==> r.Unwrap() < n
    decreases a, n
  {
    var (gcd: nat, x: int, y: int) := GcdExtended(a, n);
    assume {:axiom} Abs(x) < n;
    if gcd > 1 then
      None
    else if x >= 0 then
      Some(x)
    else
      Some(x + n)
  }

  predicate IsPrime(n: nat)
    decreases n
  {
    n > 1 &&
    forall a: int {:trigger GcdExtended(a, n)} :: 
      1 <= a < n ==>
        GcdExtended(a, n).0 == 1
  }

  lemma PrimeFieldsHaveInverse(a: nat, n: nat)
    requires IsPrime(n)
    requires 1 <= a < n
    ensures Inverse(a, n) != None
    decreases a, n
  {
    assert GcdExtended(a, n).0 == 1;
  }

  import opened Optional
}

module SubState {
  function Create(): T
  {
    SubState({}, [], {}, 0, {1, 2, 3, 4, 5, 6, 7, 8, 9}, {})
  }

  import opened Int

  type LogEntry = l: (seq<u256>, seq<u8>)
    | |l.0| <= 4
    witness ([], [])

  datatype Raw = SubState(selfDestruct: set<u160>, log: seq<LogEntry>, touched: set<(u160, u256)>, refund: int, accessedAccounts: set<u160>, accessedKeys: set<(u160, u256)>) {
    function Append(entries: seq<LogEntry>): Raw
      decreases this, entries
    {
      this.(log := this.log + entries)
    }

    function AccountDestructed(account: u160): Raw
      decreases this, account
    {
      this.(selfDestruct := this.selfDestruct + {account})
    }

    function WasAccountAccessed(account: u160): bool
      decreases this, account
    {
      account in accessedAccounts
    }

    function AccountAccessed(account: u160): Raw
      decreases this, account
    {
      var naccessed: set<u160> := accessedAccounts + {account};
      this.(accessedAccounts := naccessed)
    }

    function WasKeyAccessed(account: u160, address: u256): bool
      decreases this, account, address
    {
      (account, address) in accessedKeys
    }

    function KeyAccessed(account: u160, address: u256): Raw
      decreases this, account, address
    {
      var naccessed: set<(u160, u256)> := accessedKeys + {(account, address)};
      this.(accessedKeys := naccessed)
    }

    function ModifyRefundCounter(k: int): Raw
      decreases this, k
    {
      this.(refund := this.refund + k)
    }
  }

  type T = c: Raw
    | {1, 2, 3, 4, 5, 6, 7, 8, 9} <= c.accessedAccounts
    witness SubState({}, [], {}, 0, {1, 2, 3, 4, 5, 6, 7, 8, 9}, {})
}

module WorldState {
  const HASH_EMPTYCODE: u256 := 89477152217924674838424037953991966239322087453347756267410168184682657981552

  function CreateAccount(nonce: nat, balance: u256, storage: Storage.T, code: Code.T, hash: u256): Account
    decreases nonce, balance, storage, code, hash
  {
    Account(nonce, balance, storage, code, hash)
  }

  function DefaultAccount(): Account
  {
    CreateAccount(0, 0, Storage.Create(map[]), Code.Create([]), HASH_EMPTYCODE)
  }

  function Create(accounts: map<u160, Account>): T
    decreases accounts
  {
    WorldState(accounts, accounts)
  }

  import opened Int

  import Code

  import opened Optional

  import Storage

  import External

  datatype Account = Account(nonce: nat, balance: u256, storage: Storage.T, code: Code.T, hash: u256)

  datatype T = WorldState(accounts: map<u160, Account>, pretransactionaccounts: map<u160, Account>) {
    function Exists(account: u160): bool
      decreases this, account
    {
      account in accounts
    }

    function CanOverwrite(account: u160): bool
      requires account in accounts
      decreases this, account
    {
      var data: Account := accounts[account];
      |data.code.contents| == 0 &&
      data.nonce == 0
    }

    function isEndUser(account: u160): bool
      requires account in accounts
      decreases this, account
    {
      Code.Size(accounts[account].code) == 0
    }

    function IsEmpty(account: u160): bool
      requires account in accounts
      decreases this, account
    {
      var data: Account := accounts[account];
      Code.Size(data.code) == 0 &&
      data.nonce == 0 &&
      data.balance == 0
    }

    function IsDead(account: u160): bool
      decreases this, account
    {
      !(account in accounts) || IsEmpty(account)
    }

    function GetAccount(account: u160): Option<Account>
      decreases this, account
    {
      if account in accounts then
        Some(accounts[account])
      else
        None
    }

    function GetOrDefault(account: u160): Account
      decreases this, account
    {
      if account in accounts then
        accounts[account]
      else
        DefaultAccount()
    }

    function GetOrDefaultPretransaction(account: u160): Account
      decreases this, account
    {
      if account in pretransactionaccounts then
        pretransactionaccounts[account]
      else
        DefaultAccount()
    }

    function Put(account: u160, data: Account): T
      decreases this, account, data
    {
      this.(accounts := this.accounts[account := data])
    }

    function EnsureAccount(address: u160): T
      decreases this, address
    {
      if Exists(address) then
        this
      else
        Put(address, DefaultAccount())
    }

    function Balance(account: u160): u256
      requires account in this.accounts
      decreases this, account
    {
      accounts[account].balance
    }

    function CanDeposit(account: u160, value: u256): bool
      requires account in this.accounts
      decreases this, account, value
    {
      MAX_U256 as u256 - accounts[account].balance >= value
    }

    function CanWithdraw(account: u160, value: u256): bool
      requires account in this.accounts
      decreases this, account, value
    {
      accounts[account].balance >= value
    }

    function Withdraw(account: u160, value: u256): T
      requires account in this.accounts
      requires CanWithdraw(account, value)
      decreases this, account, value
    {
      var entry: Account := accounts[account];
      var nBalance: u256 := entry.balance - value;
      this.(accounts := this.accounts[account := entry.(balance := nBalance)])
    }

    function Deposit(account: u160, value: u256): T
      requires account in this.accounts
      requires CanDeposit(account, value)
      decreases this, account, value
    {
      var entry: Account := accounts[account];
      var nBalance: u256 := entry.balance + value;
      this.(accounts := this.accounts[account := entry.(balance := nBalance)])
    }

    function Transfer(from: u160, to: u160, value: u256): T
      requires from in this.accounts && to in this.accounts
      requires CanWithdraw(from, value) && CanDeposit(to, value)
      decreases this, from, to, value
    {
      this.Withdraw(from, value).Deposit(to, value)
    }

    function SetCode(account: u160, code: seq<u8>, hash: u256): T
      requires account in this.accounts
      requires |code| <= Code.MAX_CODE_SIZE
      decreases this, account, code, hash
    {
      var entry: Account := accounts[account];
      this.(accounts := this.accounts[account := entry.(code := Code.Create(code), hash := hash)])
    }

    function Nonce(account: u160): nat
      requires account in this.accounts
      decreases this, account
    {
      accounts[account].nonce
    }

    function IncNonce(account: u160): T
      requires account in this.accounts
      requires Nonce(account) < MAX_U64
      decreases this, account
    {
      var entry: Account := accounts[account];
      this.(accounts := this.accounts[account := entry.(nonce := entry.nonce + 1)])
    }

    function Write(account: u160, address: u256, value: u256): T
      requires account in this.accounts
      decreases this, account, address, value
    {
      var entry: Account := accounts[account];
      var pValue: u256 := Storage.Read(entry.storage, address);
      var nStorage: T := Storage.Write(entry.storage, address, value);
      WorldState(this.accounts[account := entry.(storage := nStorage)], pretransactionaccounts)
    }

    function Read(account: u160, address: u256): u256
      requires account in this.accounts
      decreases this, account, address
    {
      var entry: Account := accounts[account];
      Storage.Read(entry.storage, address)
    }
  }
}

module External {

  import opened Arrays

  import opened Int
}

module Storage {
  function Create(contents: map<u256, u256>): T
    decreases contents
  {
    Storage(contents := contents)
  }

  function Read(mem: T, address: u256): u256
    decreases mem, address
  {
    if address in mem.contents then
      mem.contents[address]
    else
      0
  }

  function Write(mem: T, address: u256, val: u256): T
    decreases mem, address, val
  {
    Storage(contents := mem.contents[address := val])
  }

  import opened Int

  datatype T = Storage(contents: map<u256, u256>)
}

module Code {
  const MAX_CODE_SIZE := 24576

  function Create(contents: seq<u8>): T
    requires |contents| <= MAX_CODE_SIZE
    decreases contents
  {
    Code(contents := contents)
  }

  function Size(c: T): u256
    decreases c
  {
    |c.contents| as u256
  }

  function DecodeUint8(c: T, address: nat): u8
    decreases c, address
  {
    if address < |c.contents| then
      c.contents[address]
    else
      0
  }

  function CodeAt(c: T, index: nat): u8
    requires 0 <= index < Size(c) as nat
    decreases c, index
  {
    c.contents[index]
  }

  function Slice(c: T, address: nat, len: nat): seq<u8>
    decreases c, address, len
  {
    Arrays.SliceAndPad(c.contents, address, len, 0)
  }

  import Arrays

  import opened Int

  datatype Raw = Code(contents: seq<u8>)

  type T = c: Raw
    | |c.contents| <= MAX_CODE_SIZE
    witness Code([])
}

module EvmFork {
  const GENISIS_BYTECODES: set<u8> := {STOP, ADD, MUL, SUB, DIV, SDIV, MOD, SMOD, ADDMOD, MULMOD, EXP, SIGNEXTEND, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, NOT, BYTE, SHL, SHR, SAR, KECCAK256, ADDRESS, BALANCE, ORIGIN, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE, CALLDATACOPY, CODESIZE, CODECOPY, GASPRICE, EXTCODESIZE, EXTCODECOPY, RETURNDATASIZE, RETURNDATACOPY, EXTCODEHASH, BLOCKHASH, COINBASE, TIMESTAMP, NUMBER, DIFFICULTY, GASLIMIT, CHAINID, SELFBALANCE, POP, MLOAD, MSTORE, MSTORE8, SLOAD, SSTORE, JUMP, JUMPI, PC, MSIZE, GAS, JUMPDEST, PUSH1, PUSH2, PUSH3, PUSH4, PUSH5, PUSH6, PUSH7, PUSH8, PUSH9, PUSH10, PUSH11, PUSH12, PUSH13, PUSH14, PUSH15, PUSH16, PUSH17, PUSH18, PUSH19, PUSH20, PUSH21, PUSH22, PUSH23, PUSH24, PUSH25, PUSH26, PUSH27, PUSH28, PUSH29, PUSH30, PUSH31, PUSH32, DUP1, DUP2, DUP3, DUP4, DUP5, DUP6, DUP7, DUP8, DUP9, DUP10, DUP11, DUP12, DUP13, DUP14, DUP15, DUP16, SWAP1, SWAP2, SWAP3, SWAP4, SWAP5, SWAP6, SWAP7, SWAP8, SWAP9, SWAP10, SWAP11, SWAP12, SWAP13, SWAP14, SWAP15, SWAP16, LOG0, LOG1, LOG2, LOG3, LOG4, EOF, CREATE, CALL, CALLCODE, RETURN, DELEGATECALL, CREATE2, STATICCALL, REVERT, INVALID, SELFDESTRUCT}

  function EipDescription(eip: nat): Option<string>
    decreases eip
  {
    match eip
    case 1153 =>
      Some("Transient storage opcodes")
    case 1559 =>
      Some("Fee market change for ETH 1.0 chain")
    case 2565 =>
      Some("ModExp Gas Cost")
    case 2929 =>
      Some("Gas cost increases for state access opcodes")
    case 2718 =>
      Some("Typed Transaction Envelope")
    case 2930 =>
      Some("Optional access lists")
    case 3198 =>
      Some("BASEFEE opcode")
    case 3529 =>
      Some("Reduction in refunds")
    case 3541 =>
      Some("Reject new contract code starting with the 0xEF byte")
    case 3554 =>
      Some("Difficulty Bomb Delay to December 2021")
    case 3651 =>
      Some("Warm COINBASE")
    case 3675 =>
      Some("Upgrade consensus to Proof-of-Stake")
    case 3855 =>
      Some("PUSH0 instruction")
    case 3860 =>
      Some("Limit and meter initcode")
    case 4345 =>
      Some("Difficulty Bomb Delay to June 2022")
    case 4399 =>
      Some("Supplant DIFFICULTY opcode with PREVRANDAO")
    case 4895 =>
      Some("Beacon chain push withdrawals as operations")
    case 5133 =>
      Some("Delaying Difficulty Bomb to mid-September 2022")
    case 5656 =>
      Some("MCOPY - Memory copying instruction")
    case _ /* _v0 */ =>
      None
  }

  function EipBytecodes(eips: seq<nat>, bytecodes: set<u8>): set<u8>
    decreases eips, bytecodes
  {
    if |eips| == 0 then
      bytecodes
    else
      match eips[0] case 1153 => EipBytecodes(eips[1..], bytecodes + {TLOAD, TSTORE}) case 3198 => EipBytecodes(eips[1..], bytecodes + {BASEFEE}) case 3855 => EipBytecodes(eips[1..], bytecodes + {PUSH0}) case 5656 => EipBytecodes(eips[1..], bytecodes + {MCOPY}) case _ /* _v1 */ => EipBytecodes(eips[1..], bytecodes)
  }

  const BERLIN_EIPS: seq<nat> := [2565, 2929, 2718, 2930]
  const LONDON_EIPS: seq<nat> := BERLIN_EIPS + [1559, 3198, 3529, 3541, 3554]
  const SHANGHAI_EIPS: seq<nat> := LONDON_EIPS + [3651, 3855, 3860, 4895]
  const CANCUN_EIPS: seq<nat> := SHANGHAI_EIPS + [1153, 5656]
  const BERLIN_BYTECODES: set<u8> := EipBytecodes(BERLIN_EIPS, GENISIS_BYTECODES)
  const LONDON_BYTECODES: set<u8> := EipBytecodes(LONDON_EIPS, GENISIS_BYTECODES)
  const SHANGHAI_BYTECODES: set<u8> := EipBytecodes(SHANGHAI_EIPS, GENISIS_BYTECODES)
  const CANCUN_BYTECODES: set<u8> := EipBytecodes(CANCUN_EIPS, GENISIS_BYTECODES)
  const BERLIN: Fork := Instance(20210415, BERLIN_EIPS, BERLIN_BYTECODES)
  const LONDON: Fork := Instance(20210805, LONDON_EIPS, LONDON_BYTECODES)
  const SHANGHAI: Fork := Instance(20230412, SHANGHAI_EIPS, SHANGHAI_BYTECODES)
  const CANCUN: Fork := Instance(20240312, CANCUN_EIPS, CANCUN_BYTECODES)

  lemma {:verify false} BerlinFacts()
    ensures BASEFEE !in BERLIN_BYTECODES
  {
  }

  lemma {:verify false} LondonFacts()
    ensures BASEFEE in LONDON_BYTECODES
  {
  }

  lemma {:verify false} ShanghaiFacts()
    ensures {PUSH0, BASEFEE} <= SHANGHAI_BYTECODES
  {
  }

  lemma {:verify false} CancunFacts()
    ensures {MCOPY, TLOAD, TSTORE} <= CANCUN_BYTECODES
  {
  }

  import opened Int

  import opened Opcode

  import opened Optional

  type EIP = (nat, string)

  datatype Fork = Instance(id: nat, eips: seq<nat>, bytecodes: set<u8>) {
    predicate IsActive(eip: nat)
      decreases this, eip
    {
      eip in this.eips
    }

    predicate IsBytecode(opcode: u8)
      decreases this, opcode
    {
      opcode in bytecodes
    }
  }
}

module Opcode {
  const STOP: u8 := 0
  const ADD: u8 := 1
  const MUL: u8 := 2
  const SUB: u8 := 3
  const DIV: u8 := 4
  const SDIV: u8 := 5
  const MOD: u8 := 6
  const SMOD: u8 := 7
  const ADDMOD: u8 := 8
  const MULMOD: u8 := 9
  const EXP: u8 := 10
  const SIGNEXTEND: u8 := 11
  const LT: u8 := 16
  const GT: u8 := 17
  const SLT: u8 := 18
  const SGT: u8 := 19
  const EQ: u8 := 20
  const ISZERO: u8 := 21
  const AND: u8 := 22
  const OR: u8 := 23
  const XOR: u8 := 24
  const NOT: u8 := 25
  const BYTE: u8 := 26
  const SHL: u8 := 27
  const SHR: u8 := 28
  const SAR: u8 := 29
  const KECCAK256: u8 := 32
  const ADDRESS: u8 := 48
  const BALANCE: u8 := 49
  const ORIGIN: u8 := 50
  const CALLER: u8 := 51
  const CALLVALUE: u8 := 52
  const CALLDATALOAD: u8 := 53
  const CALLDATASIZE: u8 := 54
  const CALLDATACOPY: u8 := 55
  const CODESIZE: u8 := 56
  const CODECOPY: u8 := 57
  const GASPRICE: u8 := 58
  const EXTCODESIZE: u8 := 59
  const EXTCODECOPY: u8 := 60
  const RETURNDATASIZE: u8 := 61
  const RETURNDATACOPY: u8 := 62
  const EXTCODEHASH: u8 := 63
  const BLOCKHASH: u8 := 64
  const COINBASE: u8 := 65
  const TIMESTAMP: u8 := 66
  const NUMBER: u8 := 67
  const DIFFICULTY: u8 := 68
  const GASLIMIT: u8 := 69
  const CHAINID: u8 := 70
  const SELFBALANCE: u8 := 71
  const BASEFEE: u8 := 72
  const POP: u8 := 80
  const MLOAD: u8 := 81
  const MSTORE: u8 := 82
  const MSTORE8: u8 := 83
  const SLOAD: u8 := 84
  const SSTORE: u8 := 85
  const JUMP: u8 := 86
  const JUMPI: u8 := 87
  const PC: u8 := 88
  const MSIZE: u8 := 89
  const GAS: u8 := 90
  const JUMPDEST: u8 := 91
  const TLOAD: u8 := 92
  const TSTORE: u8 := 93
  const MCOPY: u8 := 94
  const PUSH0: u8 := 95
  const PUSH1: u8 := 96
  const PUSH2: u8 := 97
  const PUSH3: u8 := 98
  const PUSH4: u8 := 99
  const PUSH5: u8 := 100
  const PUSH6: u8 := 101
  const PUSH7: u8 := 102
  const PUSH8: u8 := 103
  const PUSH9: u8 := 104
  const PUSH10: u8 := 105
  const PUSH11: u8 := 106
  const PUSH12: u8 := 107
  const PUSH13: u8 := 108
  const PUSH14: u8 := 109
  const PUSH15: u8 := 110
  const PUSH16: u8 := 111
  const PUSH17: u8 := 112
  const PUSH18: u8 := 113
  const PUSH19: u8 := 114
  const PUSH20: u8 := 115
  const PUSH21: u8 := 116
  const PUSH22: u8 := 117
  const PUSH23: u8 := 118
  const PUSH24: u8 := 119
  const PUSH25: u8 := 120
  const PUSH26: u8 := 121
  const PUSH27: u8 := 122
  const PUSH28: u8 := 123
  const PUSH29: u8 := 124
  const PUSH30: u8 := 125
  const PUSH31: u8 := 126
  const PUSH32: u8 := 127
  const DUP1: u8 := 128
  const DUP2: u8 := 129
  const DUP3: u8 := 130
  const DUP4: u8 := 131
  const DUP5: u8 := 132
  const DUP6: u8 := 133
  const DUP7: u8 := 134
  const DUP8: u8 := 135
  const DUP9: u8 := 136
  const DUP10: u8 := 137
  const DUP11: u8 := 138
  const DUP12: u8 := 139
  const DUP13: u8 := 140
  const DUP14: u8 := 141
  const DUP15: u8 := 142
  const DUP16: u8 := 143
  const SWAP1: u8 := 144
  const SWAP2: u8 := 145
  const SWAP3: u8 := 146
  const SWAP4: u8 := 147
  const SWAP5: u8 := 148
  const SWAP6: u8 := 149
  const SWAP7: u8 := 150
  const SWAP8: u8 := 151
  const SWAP9: u8 := 152
  const SWAP10: u8 := 153
  const SWAP11: u8 := 154
  const SWAP12: u8 := 155
  const SWAP13: u8 := 156
  const SWAP14: u8 := 157
  const SWAP15: u8 := 158
  const SWAP16: u8 := 159
  const LOG0: u8 := 160
  const LOG1: u8 := 161
  const LOG2: u8 := 162
  const LOG3: u8 := 163
  const LOG4: u8 := 164
  const EOF: u8 := 239
  const CREATE: u8 := 240
  const CALL: u8 := 241
  const CALLCODE: u8 := 242
  const RETURN: u8 := 243
  const DELEGATECALL: u8 := 244
  const CREATE2: u8 := 245
  const STATICCALL: u8 := 250
  const REVERT: u8 := 253
  const INVALID: u8 := 254
  const SELFDESTRUCT: u8 := 255

  import opened Int
}

module Context {
  function Create(sender: u160, origin: u160, recipient: u160, callValue: u256, callData: Array<u8>, writePermission: bool, gasPrice: u256, block: Block): T
    decreases sender, origin, recipient, callValue, callData, writePermission, gasPrice, block
  {
    Context(sender, origin, address := recipient, callValue := callValue, callData := callData, returnData := [], writePermission := writePermission, gasPrice := gasPrice, block := block)
  }

  const DEFAULT: T := Create(0, 0, 0, 0, [], true, 0, Block.Info(0, 0, 0, 0, 0, 0, 0))

  import opened Arrays

  import opened Int

  import opened Optional

  import ByteUtils

  datatype Block = Info(coinBase: u256, timeStamp: u256, number: u256, difficulty: u256, gasLimit: u256, chainID: u256, baseFee: u256)

  datatype T = Context(sender: u160, origin: u160, address: u160, callValue: u256, callData: Array<u8>, returnData: Array<u8>, writePermission: bool, gasPrice: u256, block: Block) {
    function CallDataSize(): u256
      decreases this
    {
      |this.callData| as u256
    }

    function CallDataRead(loc: u256): u256
      decreases this, loc
    {
      ByteUtils.ReadUint256(this.callData, loc as nat)
    }

    function CallDataSlice(loc: u256, len: nat): (data: seq<u8>)
      ensures |data| == len
      decreases this, loc, len
    {
      Arrays.SliceAndPad(this.callData, loc as nat, len, 0)
    }

    function ReturnDataSize(): u256
      decreases this
    {
      |this.returnData| as u256
    }

    function ReturnDataSlice(loc: nat, len: nat): (data: seq<u8>)
      requires loc + len <= |this.returnData|
      ensures |data| == len
      decreases this, loc, len
    {
      Arrays.SliceAndPad(this.returnData, loc, len, 0)
    }

    function SetReturnData(data: Array<u8>): T
      decreases this, data
    {
      this.(returnData := data)
    }
  }
}

module Memory {
  function Create(): T
  {
    Memory(contents := [])
  }

  function Size(mem: T): nat
    decreases mem
  {
    |mem.contents|
  }

  function Expand(mem: T, address: nat): (r: T)
    ensures |r.contents| > address
    ensures address >= |mem.contents| ==> |r.contents| % 32 == 0 && |r.contents| - 32 <= address
    decreases mem, address
  {
    if address < |mem.contents| then
      mem
    else
      var extLength: nat := SmallestLarg32(address); mem.(contents := mem.contents + ByteUtils.Padding(extLength - |mem.contents|))
  }

  function SmallestLarg32(k: nat): (x: nat)
    ensures x > k
    ensures x % 32 == 0
    ensures x - 32 <= k
    decreases k
  {
    (k / 32 + 1) * 32
  }

  function ExpandMem(mem: T, address: nat, len: nat): (r: T)
    requires len > 0
    decreases mem, address, len
  {
    Expand(mem, address + len - 1)
  }

  function ReadUint256(mem: T, address: nat): u256
    requires address + 31 < |mem.contents|
    decreases mem, address
  {
    ByteUtils.ReadUint256(mem.contents, address)
  }

  function WriteUint8(mem: T, address: nat, val: u8): T
    requires address < |mem.contents|
    decreases mem, address, val
  {
    Memory(contents := mem.contents[address := val])
  }

  function WriteUint256(mem: T, address: nat, val: u256): (mem': T)
    requires address + 31 < |mem.contents|
    ensures Arrays.EqualsExcept(mem.contents, mem'.contents, address, 32)
    decreases mem, address, val
  {
    var ncontents: seq<u8> := ByteUtils.WriteUint256(mem.contents, address, val);
    Memory(contents := ncontents)
  }

  function Slice(mem: T, address: nat, len: nat): (result: seq<u8>)
    ensures |result| == len
    decreases mem, address, len
  {
    Arrays.SliceAndPad(mem.contents, address, len, 0)
  }

  function Copy(mem: T, address: nat, data: seq<u8>): (mem': T)
    requires |data| == 0 || address + |data| <= |mem.contents|
    decreases mem, address, data
  {
    if |data| == 0 then
      mem
    else
      Memory(Arrays.Copy(data, mem.contents, address))
  }

  import opened Int

  import U256

  import Arrays

  import ByteUtils

  datatype T = Memory(contents: seq<u8>)
}

module EvmState {
  const G_CODEDEPOSIT: nat := 200
  const EVM_WITNESS: Raw := EVM(BERLIN, Context.DEFAULT, Precompiled.DEFAULT, WorldState.Create(map[0 := WorldState.DefaultAccount()]), EmptyEvmStack, Memory.Create(), TransientStorage.Create(), Code.Create([]), SubState.Create(), 0, 0)

  function Call(world: WorldState.T, transient: TransientStorage.T, ctx: Context.T, fork: Fork, precompiled: Precompiled.T, substate: SubState.T, codeAddress: u160, value: u256, gas: nat, depth: nat): State
    requires world.Exists(ctx.sender)
    decreases world, transient, ctx, fork, precompiled, substate, codeAddress, value, gas, depth
  {
    var address: u160 := ctx.address;
    if depth > 1024 || !world.CanWithdraw(ctx.sender, value) then
      ERROR(REVERTS, gas)
    else
      var w: T := world.EnsureAccount(address); if !w.CanDeposit(address, value) then ERROR(BALANCE_OVERFLOW) else var nw: T := w.Transfer(ctx.sender, address, value); if codeAddress >= 1 && codeAddress <= 9 then match precompiled.Call(codeAddress, ctx.callData) case None() => ERROR(INVALID_PRECONDITION) case Some((data, gascost)) => if gas >= gascost then RETURNS(gas - gascost, data, nw, transient, substate) else ERROR(INSUFFICIENT_GAS) else var cod: Code.T := w.GetOrDefault(codeAddress).code; if |cod.contents| == 0 then RETURNS(gas, [], nw, transient, substate) else var stack: EvmStack := EmptyEvmStack; var mem: T := Memory.Create(); var evm: Raw := EVM(fork, ctx, precompiled, nw, stack, mem, transient, cod, substate, gas, 0); EXECUTING(evm)
  }

  function Create(world: WorldState.T, transient: TransientStorage.T, ctx: Context.T, fork: Fork, precompiled: Precompiled.T, substate: SubState.T, initcode: seq<u8>, gas: nat, depth: nat): State
    requires |initcode| <= Code.MAX_CODE_SIZE
    requires world.Exists(ctx.sender)
    decreases world, transient, ctx, fork, precompiled, substate, initcode, gas, depth
  {
    var endowment: u256 := ctx.callValue;
    if depth > 1024 || !world.CanWithdraw(ctx.sender, endowment) || !ctx.writePermission then
      ERROR(REVERTS, gas)
    else if world.Exists(ctx.address) && !world.CanOverwrite(ctx.address) then
      ERROR(ACCOUNT_COLLISION)
    else
      var storage: T := Storage.Create(map[]); var account: Account := WorldState.CreateAccount(1, endowment, storage, Code.Create([]), WorldState.HASH_EMPTYCODE); var w: T := world.Put(ctx.address, account); var nw: T := w.Withdraw(ctx.sender, endowment); if |initcode| == 0 then RETURNS(gas, [], nw, transient, substate) else var stack: EvmStack := EmptyEvmStack; var mem: T := Memory.Create(); var cod: T := Code.Create(initcode); var ss: Raw := substate.AccountAccessed(ctx.address); var evm: Raw := EVM(fork, ctx, precompiled, nw, stack, mem, transient, cod, ss, gas, 0); EXECUTING(evm)
  }

  import opened Int

  import opened Arrays

  import opened Stack

  import Memory

  import Storage

  import WorldState

  import Context

  import SubState

  import TransientStorage

  import Code

  import opened EvmFork

  import Opcode

  import Precompiled

  import opened Optional

  datatype Raw = EVM(fork: Fork, context: Context.T, precompiled: Precompiled.T, world: WorldState.T, stack: EvmStack, memory: Memory.T, transient: TransientStorage.T, code: Code.T, substate: SubState.T, gas: nat, pc: nat)

  type T = c: Raw
    | c.context.address in c.world.accounts
    witness EVM_WITNESS

  type ExecutingState = s: State
    | s.EXECUTING?
    witness EXECUTING(EVM_WITNESS)

  type TerminatedState = s: State
    | s.RETURNS? || s.ERROR?
    witness ERROR(INSUFFICIENT_GAS)

  datatype Error = REVERTS | INSUFFICIENT_GAS | INSUFFICIENT_FUNDS | INVALID_OPCODE | STACK_UNDERFLOW | STACK_OVERFLOW | MEMORY_OVERFLOW | BALANCE_OVERFLOW | RETURNDATA_OVERFLOW | INVALID_JUMPDEST | INVALID_PRECONDITION | CODESIZE_EXCEEDED | CALLDEPTH_EXCEEDED | ACCOUNT_COLLISION | WRITE_PROTECTION_VIOLATED

  datatype State = EXECUTING(evm: T) | ERROR(error: Error, gas: nat := 0, data: Array<u8> := []) | RETURNS(gas: nat, data: Array<u8>, world: WorldState.T, transient: TransientStorage.T, substate: SubState.T) | CONTINUING(Continuation) {
    function Unwrap(): T
      requires this.EXECUTING?
      decreases this
    {
      this.evm
    }

    function IsRevert(): bool
      decreases this
    {
      this.ERROR? &&
      this.error == REVERTS
    }

    function Fork(): Fork
      requires this.EXECUTING?
      decreases this
    {
      this.evm.fork
    }

    function Gas(): nat
      decreases this
    {
      match this
      case EXECUTING(evm) =>
        evm.gas
      case RETURNS(g, _ /* _v1 */, _ /* _v2 */, _ /* _v3 */, _ /* _v4 */) =>
        g
      case ERROR(_ /* _v5 */, g, _ /* _v6 */) =>
        g
      case CONTINUING(cc) =>
        cc.evm.gas
    }

    function UseGas(k: nat): State
      requires this.EXECUTING?
      decreases this, k
    {
      if this.Gas() < k as nat then
        ERROR(INSUFFICIENT_GAS)
      else
        EXECUTING(evm.(gas := this.Gas() - k as nat))
    }

    function Refund(k: nat): State
      requires this.EXECUTING?
      decreases this, k
    {
      EXECUTING(evm.(gas := this.Gas() + k as nat))
    }

    function PC(): nat
      requires this.EXECUTING?
      decreases this
    {
      this.evm.pc
    }

    predicate IsEipActive(eip: nat)
      requires this.EXECUTING?
      decreases this, eip
    {
      this.evm.fork.IsActive(eip)
    }

    function WritesPermitted(): bool
      requires this.EXECUTING?
      decreases this
    {
      this.evm.context.writePermission
    }

    function Expand(address: nat, len: nat): (s': ExecutingState)
      requires this.EXECUTING?
      ensures MemSize() <= s'.MemSize()
      ensures address + len < MemSize() ==> evm.memory == s'.evm.memory
      decreases this, address, len
    {
      if len == 0 then
        this
      else
        var last: int := address + len - 1; EXECUTING(evm.(memory := Memory.Expand(evm.memory, last)))
    }

    function MemSize(): nat
      requires this.EXECUTING?
      decreases this
    {
      Memory.Size(evm.memory)
    }

    function Read(address: nat): u256
      requires this.EXECUTING?
      requires address + 31 < Memory.Size(evm.memory)
      decreases this, address
    {
      Memory.ReadUint256(evm.memory, address)
    }

    function Write(address: nat, val: u256): ExecutingState
      requires this.EXECUTING?
      requires address + 31 < Memory.Size(evm.memory)
      decreases this, address, val
    {
      EXECUTING(evm.(memory := Memory.WriteUint256(evm.memory, address, val)))
    }

    function Write8(address: nat, val: u8): ExecutingState
      requires this.EXECUTING?
      requires address < Memory.Size(evm.memory)
      decreases this, address, val
    {
      EXECUTING(evm.(memory := Memory.WriteUint8(evm.memory, address, val)))
    }

    function Copy(address: nat, data: seq<u8>): ExecutingState
      requires this.EXECUTING?
      requires |data| == 0 || address + |data| <= Memory.Size(evm.memory)
      decreases this, address, data
    {
      EXECUTING(evm.(memory := Memory.Copy(evm.memory, address, data)))
    }

    function Store(address: u256, val: u256): ExecutingState
      requires this.EXECUTING?
      decreases this, address, val
    {
      var account: u160 := evm.context.address;
      EXECUTING(evm.(world := evm.world.Write(account, address, val)))
    }

    function Load(address: u256): u256
      requires this.EXECUTING?
      decreases this, address
    {
      var account: u160 := evm.context.address;
      evm.world.Read(account, address)
    }

    function TransientStore(address: u256, val: u256): ExecutingState
      requires this.EXECUTING?
      decreases this, address, val
    {
      var account: u160 := evm.context.address;
      EXECUTING(evm.(transient := evm.transient.Write(account, address, val)))
    }

    function TransientLoad(address: u256): u256
      requires this.EXECUTING?
      decreases this, address
    {
      var account: u160 := evm.context.address;
      evm.transient.Read(account, address)
    }

    function IsEmpty(account: u160): bool
      requires this.EXECUTING?
      requires account in evm.world.accounts
      decreases this, account
    {
      var data: Account := evm.world.accounts[account];
      Code.Size(data.code) == 0 &&
      data.nonce == 0 &&
      data.balance == 0
    }

    function IsDead(account: u160): bool
      requires this.EXECUTING?
      decreases this, account
    {
      !(account in evm.world.accounts) || IsEmpty(account)
    }

    function Exists(account: u160): bool
      requires this.EXECUTING?
      decreases this, account
    {
      evm.world.Exists(account)
    }

    function IncNonce(): ExecutingState
      requires this.EXECUTING?
      requires evm.world.Nonce(evm.context.address) < MAX_U64
      decreases this
    {
      EXECUTING(evm.(world := evm.world.IncNonce(evm.context.address)))
    }

    function GetAccount(account: u160): Option<WorldState.Account>
      requires this.EXECUTING?
      decreases this, account
    {
      if account in evm.world.accounts then
        Some(evm.world.accounts[account])
      else
        None
    }

    function CreateAccount(address: u160, nonce: nat, balance: u256, storage: map<u256, u256>, code: seq<u8>): ExecutingState
      requires this.EXECUTING?
      requires !evm.world.Exists(address)
      requires |code| <= Code.MAX_CODE_SIZE
      decreases this, address, nonce, balance, storage, code
    {
      var hash: u256 := evm.precompiled.Sha3(code);
      var data: Account := WorldState.CreateAccount(nonce, balance, Storage.Create(storage), Code.Create(code), hash);
      EXECUTING(evm.(world := evm.world.Put(address, data)))
    }

    function AccountAccessed(account: u160): ExecutingState
      requires this.EXECUTING?
      decreases this, account
    {
      EXECUTING(evm.(substate := evm.substate.AccountAccessed(account)))
    }

    function ModifyRefundCounter(k: int): ExecutingState
      requires this.EXECUTING?
      decreases this, k
    {
      EXECUTING(evm.(substate := evm.substate.ModifyRefundCounter(k)))
    }

    function WasAccountAccessed(account: u160): bool
      requires this.EXECUTING?
      decreases this, account
    {
      evm.substate.WasAccountAccessed(account)
    }

    function KeyAccessed(address: u256): ExecutingState
      requires this.EXECUTING?
      decreases this, address
    {
      var account: u160 := evm.context.address;
      EXECUTING(evm.(substate := evm.substate.KeyAccessed(account, address)))
    }

    function WasKeyAccessed(address: u256): bool
      requires this.EXECUTING?
      decreases this, address
    {
      var account: u160 := evm.context.address;
      evm.substate.WasKeyAccessed(account, address)
    }

    function Merge(world: WorldState.T, transient: TransientStorage.T, substate: SubState.T): ExecutingState
      requires this.EXECUTING?
      requires world.Exists(evm.context.address)
      decreases this, world, transient, substate
    {
      EXECUTING(evm.(world := world, transient := transient, substate := substate))
    }

    function Decode(): u8
      requires this.EXECUTING?
      decreases this
    {
      Code.DecodeUint8(evm.code, evm.pc as nat)
    }

    function OpDecode(): Option<u8>
      decreases this
    {
      if this.EXECUTING? then
        Some(Code.DecodeUint8(evm.code, evm.pc as nat))
      else
        None
    }

    function Goto(k: u256): ExecutingState
      requires this.EXECUTING?
      decreases this, k
    {
      EXECUTING(evm.(pc := k as nat))
    }

    function Next(): ExecutingState
      requires this.EXECUTING?
      decreases this
    {
      EXECUTING(evm.(pc := evm.pc + 1))
    }

    function Skip(k: nat): ExecutingState
      requires this.EXECUTING?
      decreases this, k
    {
      var pc_k: int := evm.pc as nat + k;
      EXECUTING(evm.(pc := pc_k))
    }

    function Operands(): nat
      requires this.EXECUTING?
      decreases this
    {
      evm.stack.Size()
    }

    function GetStack(): EvmStack
      requires this.EXECUTING?
      decreases this
    {
      this.evm.stack
    }

    function Capacity(): nat
      requires this.EXECUTING?
      decreases this
    {
      evm.stack.Capacity()
    }

    function Push(v: u256): ExecutingState
      requires this.EXECUTING?
      requires Capacity() > 0
      decreases this, v
    {
      EXECUTING(evm.(stack := GetStack().Push(v)))
    }

    function Peek(k: nat): u256
      requires this.EXECUTING?
      requires k < Operands()
      decreases this, k
    {
      GetStack().Peek(k)
    }

    function PeekN(n: nat): (r: seq<u256>)
      requires this.EXECUTING?
      requires n <= Operands()
      decreases this, n
    {
      GetStack().PeekN(n)
    }

    function SlicePeek(l: nat, u: nat): (r: EvmStack)
      requires this.EXECUTING?
      requires l <= u <= Operands()
      ensures r.Size() == u - l
      decreases this, l, u
    {
      GetStack().Slice(l, u)
    }

    function Pop(n: nat := 1): ExecutingState
      requires this.EXECUTING?
      requires n >= 1
      requires Operands() >= n
      decreases this, n
    {
      EXECUTING(evm.(stack := GetStack().PopN(n)))
    }

    function Swap(k: nat): ExecutingState
      requires this.EXECUTING?
      requires Operands() > k > 0
      decreases this, k
    {
      EXECUTING(evm.(stack := GetStack().Swap(k)))
    }

    function Log(entries: seq<SubState.LogEntry>): ExecutingState
      requires this.EXECUTING?
      decreases this, entries
    {
      EXECUTING(evm.(substate := evm.substate.Append(entries)))
    }

    function CodeOperands(): int
      requires this.EXECUTING?
      decreases this
    {
      Code.Size(evm.code) as nat - (evm.pc as nat + 1)
    }

    function SetReturnData(data: seq<u8>): ExecutingState
      requires this.EXECUTING?
      requires |data| < TWO_256
      decreases this, data
    {
      EXECUTING(evm.(context := evm.context.SetReturnData(data)))
    }

    function CodeAtIndex(index: nat): u8
      requires this.EXECUTING?
      decreases this, index
    {
      if index < Code.Size(evm.code) as nat then
        Code.CodeAt(evm.code, index)
      else
        Opcode.STOP
    }

    function CodeAtPC(): u8
      requires this.EXECUTING?
      decreases this
    {
      CodeAtIndex(PC())
    }

    predicate IsInstructionBoundary(pc: int)
      requires this.EXECUTING?
      decreases this, pc
    {
      var len: nat := Code.Size(evm.code) as nat;
      pc >= 0 &&
      pc < len
    }

    predicate IsJumpDest(pc: u256)
      requires this.EXECUTING?
      decreases this, pc
    {
      this.IsInstructionBoundary(pc as nat) &&
      Code.DecodeUint8(evm.code, pc as nat) == Opcode.JUMPDEST
    }
  }

  datatype Continuation = CALLS(evm: T, sender: u160, recipient: u160, code: u160, gas: nat, callValue: u256, delegateValue: u256, callData: seq<u8>, writePermission: bool, outOffset: nat, outSize: nat) | CREATES(evm: T, gas: nat, endowment: u256, initcode: seq<u8>, salt: Option<u256>) {
    function CallEnter(depth: nat): State
      requires this.CALLS?
      requires |callData| <= MAX_U256
      requires evm.world.Exists(sender)
      decreases this, depth
    {
      var origin: u160 := evm.context.origin;
      var gasPrice: u256 := evm.context.gasPrice;
      var block: Block := evm.context.block;
      var precompiled: Precompiled.T := evm.precompiled;
      var ctx: T := Context.Create(sender, origin, recipient, delegateValue, callData, writePermission, gasPrice, block);
      Call(evm.world, evm.transient, ctx, evm.fork, precompiled, evm.substate, code, callValue, gas, depth + 1)
    }

    function CallReturn(vm: TerminatedState): (nst: State)
      requires this.CALLS?
      requires outSize == 0 || Memory.Size(evm.memory) >= outOffset + outSize
      requires vm.RETURNS? ==> vm.world.Exists(evm.context.address)
      decreases this, vm
    {
      var st: State := EXECUTING(evm);
      if st.Capacity() >= 1 then
        var exitCode: u256 := if vm.RETURNS? then 1 else 0;
        if vm.ERROR? && vm.error != REVERTS then
          st.Push(0).SetReturnData([])
        else
          var m: int := Min(|vm.data|, outSize); var data: seq<u8> := vm.data[0 .. m]; var nst: State := if vm.RETURNS? then st.Merge(vm.world, vm.transient, vm.substate) else st; nst.Push(exitCode).Refund(vm.gas).SetReturnData(vm.data).Copy(outOffset, data)
      else
        ERROR(STACK_OVERFLOW)
    }

    function CreateEnter(depth: nat, address: u160, initcode: seq<u8>): State
      requires this.CREATES?
      requires |initcode| <= Code.MAX_CODE_SIZE
      requires evm.world.Exists(evm.context.address)
      decreases this, depth, address, initcode
    {
      var sender: u160 := evm.context.address;
      var origin: u160 := evm.context.origin;
      var gasPrice: u256 := evm.context.gasPrice;
      var block: Block := evm.context.block;
      var precompiled: Precompiled.T := evm.precompiled;
      var ctx: T := Context.Create(sender, origin, address, endowment, [], evm.context.writePermission, gasPrice, block);
      Create(evm.world, evm.transient, ctx, evm.fork, precompiled, evm.substate, initcode, gas, depth + 1)
    }

    function CreateReturn(vm: TerminatedState, address: u160): (nst: State)
      requires this.CREATES?
      requires vm.RETURNS? ==> vm.world.Exists(evm.context.address)
      requires vm.RETURNS? ==> vm.world.Exists(address)
      decreases this, vm, address
    {
      var st: State := EXECUTING(evm);
      if st.Capacity() >= 1 then
        if vm.ERROR? then
          var nst: ExecutingState := st.AccountAccessed(address).Push(0);
          if vm.IsRevert() then
            nst.Refund(vm.gas).SetReturnData(vm.data)
          else
            nst.SetReturnData([])
        else
          assert vm.world.Exists(evm.context.address); var depositcost: int := G_CODEDEPOSIT * |vm.data|; if |vm.data| > Code.MAX_CODE_SIZE then st.Push(0).SetReturnData([]) else if this.evm.fork.IsActive(3541) && |vm.data| > 0 && vm.data[0] == Opcode.EOF then st.Push(0).SetReturnData([]) else if vm.gas < depositcost then st.Push(0).SetReturnData([]) else var hash: u256 := evm.precompiled.Sha3(vm.data); var nworld: T := vm.world.SetCode(address, vm.data, hash); var nvm: Raw := vm.substate.AccountAccessed(address); st.Refund(vm.gas - depositcost).Merge(nworld, vm.transient, nvm).Push(address as u256).SetReturnData([])
      else
        ERROR(STACK_OVERFLOW)
    }
  }
}

module TransientStorage {
  function Create(): T
  {
    TransientStorage(map[])
  }

  import opened Int

  import Storage

  datatype T = TransientStorage(contents: map<u160, Storage.T>) {
    function Write(account: u160, address: u256, value: u256): T
      decreases this, account, address, value
    {
      var entry: T := if account in this.contents then this.contents[account] else Storage.Create(map[]);
      var nStorage: T := Storage.Write(entry, address, value);
      TransientStorage(this.contents[account := nStorage])
    }

    function Read(account: u160, address: u256): u256
      decreases this, account, address
    {
      if account in this.contents then
        var entry: Storage.T := this.contents[account];
        Storage.Read(entry, address)
      else
        0
    }
  }
}

module Stack {
  const CAPACITY: nat := 1024
  const Empty := Stack(contents := [])

  function Make(xs: seq<u256>): EvmStack
    requires |xs| <= CAPACITY
    decreases xs
  {
    Stack(contents := xs)
  }

  const EmptyEvmStack: EvmStack := Stack([])

  import opened Int

  type ValidStackContent = xs: seq<u256>
    | |xs| <= CAPACITY

  datatype EvmStack = Stack(contents: ValidStackContent) {
    function Size(): nat
      decreases this
    {
      |contents|
    }

    function Capacity(): nat
      decreases this
    {
      CAPACITY - |contents|
    }

    function Push(val: u256): EvmStack
      requires this.Size() < CAPACITY
      decreases this, val
    {
      Stack(contents := [val] + contents)
    }

    function Peek(k: nat): u256
      requires k >= 0 && k < this.Size()
      decreases this, k
    {
      contents[k]
    }

    function PeekN(n: nat): (r: seq<u256>)
      requires this.Size() >= n
      ensures |r| == n
      decreases this, n
    {
      contents[..n]
    }

    function Pop(): EvmStack
      requires this.Size() > 0
      decreases this
    {
      Stack(contents := contents[1..])
    }

    function PopN(n: nat): EvmStack
      requires this.Size() >= n
      decreases this, n
    {
      Stack(contents := contents[n..])
    }

    function Swap(k: nat): EvmStack
      requires this.Size() > k > 0
      decreases this, k
    {
      var top: u256 := contents[0];
      var kth: u256 := contents[k];
      Stack(contents := contents[0 := kth][k := top])
    }

    function Slice(l: nat, u: nat): (r: EvmStack)
      requires l <= u <= this.Size()
      decreases this, l, u
    {
      Stack(contents[l .. u])
    }
  }
}

module Precompiled {
  const DEFAULT: T := Dispatcher((data: Array<u8>, v: u8, r: u256, s: u256) => data, (data: Array<u8>) => data, (data: Array<u8>) => data, (data: Array<u8>) => data, (data: seq<u8>) => 0)
  const G_ECDSA := 3000
  const SECP256K1N: u256 := 115792089237316195423570985008687907852837564279074904382605163141518161494337

  function CallEcdsaRecover(fn: EcdsaRecoverFn, data: Array<u8>): Option<(Array<u8>, nat)>
    decreases data
  {
    var h: seq<u8> := Arrays.SliceAndPad(data, 0, 32, 0);
    var v: u256 := ByteUtils.ReadUint256(data, 32);
    var r: u256 := ByteUtils.ReadUint256(data, 64);
    var s: u256 := ByteUtils.ReadUint256(data, 96);
    var key: Array<u8> := if !(v in {27, 28}) || r == 0 || r >= SECP256K1N || s == 0 || s >= SECP256K1N then [] else fn(h, v as u8, r, s);
    Some((key, G_ECDSA))
  }

  function CallSha256(fn: Sha256Fn, data: Array<u8>): Option<(Array<u8>, nat)>
    decreases data
  {
    Some((fn(data), CostSha256(data)))
  }

  function CostSha256(data: Array<u8>): nat
    decreases data
  {
    var d: int := Int.RoundUp(|data|, 32) / 32;
    60 + 12 * d
  }

  function CallRipEmd160(fn: RipEmd160Fn, data: Array<u8>): Option<(Array<u8>, nat)>
    decreases data
  {
    Some((fn(data), CostRipEmd160(data)))
  }

  function CostRipEmd160(data: Array<u8>): nat
    decreases data
  {
    var d: int := Int.RoundUp(|data|, 32) / 32;
    600 + 120 * d
  }

  function CallID(data: Array<u8>): Option<(Array<u8>, nat)>
    decreases data
  {
    Some((data, CostID(data)))
  }

  function CostID(data: Array<u8>): nat
    decreases data
  {
    var d: int := Int.RoundUp(|data|, 32) / 32;
    15 + 3 * d
  }

  const G_QUADDIVISOR: nat := 3

  function {:verify false} CallModExp(data: Array<u8>): Option<(Array<u8>, nat)>
    decreases data
  {
    var lB: nat := ByteUtils.ReadUint256(data, 0) as nat;
    var lE: nat := ByteUtils.ReadUint256(data, 32) as nat;
    var lM: nat := ByteUtils.ReadUint256(data, 64) as nat;
    var output: Array<u8> := if lB == 0 && lM == 0 then [] else var M_bytes: seq<u8> := Arrays.SliceAndPad(data, 96 + lB + lE, lM, 0); var M: nat := Int.FromBytes(M_bytes); if M != 0 then var B_bytes: seq<u8> := Arrays.SliceAndPad(data, 96, lB, 0); var E_bytes: seq<u8> := Arrays.SliceAndPad(data, 96 + lB, lE, 0); var E: nat := Int.FromBytes(E_bytes); var B: nat := Int.FromBytes(B_bytes); var modexp: nat := MathUtils.ModPow(B, E, M); var modexp_bytes: seq<u8> := Int.ToBytes(modexp); Int.LemmaLengthToBytes(modexp, M); Int.LemmaLengthFromBytes(M, M_bytes); ByteUtils.LeftPad(modexp_bytes, lM) else seq(lM, (i: int) => 0);
    var lEp: nat := LenEp(lB, lE, data);
    var gascost: int := Int.Max(200, f(Int.Max(lM, lB)) * Int.Max(lEp, 1) / G_QUADDIVISOR);
    Some((output, gascost))
  }

  function f(x: nat): nat
    decreases x
  {
    var xd8: int := Int.RoundUp(x, 8) / 8;
    xd8 * xd8
  }

  function LenEp(lB: nat, lE: nat, data: Array<u8>): nat
    decreases lB, lE, data
  {
    if lE <= 32 then
      var E_bytes: seq<u8> := Arrays.SliceAndPad(data, 96 + lB, lE, 0);
      var w: u256 := ByteUtils.ReadUint256(ByteUtils.LeftPad(E_bytes, 32), 0);
      if w == 0 then
        0
      else
        U256.Log2(w)
    else
      var w: u256 := ByteUtils.ReadUint256(data, 96 + lB); var g: int := 8 * (lE - 32); if 32 < lE && w != 0 then g + U256.Log2(w) else g
  }

  const G_BNADD := 150

  function CallBnAdd(data: Array<u8>): Option<(Array<u8>, nat)>
    decreases data
  {
    AltBn128.IsPrimeField();
    var x0: Option<AltBn128.Element> := BNF(ByteUtils.ReadUint256(data, 0) as nat);
    var y0: Option<AltBn128.Element> := BNF(ByteUtils.ReadUint256(data, 32) as nat);
    var x1: Option<AltBn128.Element> := BNF(ByteUtils.ReadUint256(data, 64) as nat);
    var y1: Option<AltBn128.Element> := BNF(ByteUtils.ReadUint256(data, 96) as nat);
    if x0 == None || y0 == None || x1 == None || y1 == None then
      None
    else
      var p0: Option<AltBn128.Point> := BNP(x0.Unwrap(), y0.Unwrap()); var p1: Option<AltBn128.Point> := BNP(x1.Unwrap(), y1.Unwrap()); if p0 == None || p1 == None then None else var p: Point := p0.Unwrap().Add(p1.Unwrap()); var (r_x: u256, r_y: u256) := if p == Infinity then (0, 0) else var Pair(p_x: Element, p_y: Element) := p; (p_x.n as u256, p_y.n as u256); var bytes: Array<u8> := U256.ToBytes(r_x) + U256.ToBytes(r_y); assert |bytes| == 64; Some((bytes, G_BNADD))
  }

  function BNF(val: nat): (r: Option<AltBn128.Element>)
    ensures r == None || r.Unwrap().Value?
    decreases val
  {
    if val < ALT_BN128_PRIME then
      Some(AltBn128.Value(val))
    else
      None
  }

  function BNP(x: AltBn128.Element, y: AltBn128.Element): (r: Option<AltBn128.Point>)
    decreases x, y
  {
    if AltBn128.OnCurve(x, y) then
      var bnp: Point := AltBn128.Pair(x, y);
      Some(bnp)
    else if x.n == 0 && y.n == 0 then
      var bnp: Point := AltBn128.Infinity;
      Some(bnp)
    else
      None
  }

  const G_BNMUL := 6000

  function CallBnMul(data: Array<u8>): Option<(Array<u8>, nat)>
    decreases data
  {
    AltBn128.IsPrimeField();
    var x0: Option<AltBn128.Element> := BNF(ByteUtils.ReadUint256(data, 0) as nat);
    var y0: Option<AltBn128.Element> := BNF(ByteUtils.ReadUint256(data, 32) as nat);
    var n: u256 := ByteUtils.ReadUint256(data, 64);
    if x0 == None || y0 == None then
      None
    else
      var p0: Option<AltBn128.Point> := BNP(x0.Unwrap(), y0.Unwrap()); if p0 == None then None else var p: Point := p0.Unwrap().Mul(n as nat); var (r_x: u256, r_y: u256) := if p == Infinity then (0, 0) else var Pair(p_x: Element, p_y: Element) := p; (p_x.n as u256, p_y.n as u256); var bytes: Array<u8> := U256.ToBytes(r_x) + U256.ToBytes(r_y); assert |bytes| == 64; Some((bytes, G_BNMUL))
  }

  function CallSnarkV(data: Array<u8>): Option<(seq<u8>, nat)>
    decreases data
  {
    Some((data, CostSnarkV(data)))
  }

  function CostSnarkV(data: Array<u8>): nat
    decreases data
  {
    34000 * |data| / 192 + 45000
  }

  function CallBlake2f(fn: Blake2Fn, data: Array<u8>): Option<(Array<u8>, nat)>
    decreases data
  {
    if |data| == 213 && data[212] in {0, 1} then
      var r: nat := U32.Read(data, 0) as nat;
      Some((fn(data), r))
    else
      None
  }

  import opened Int

  import opened Arrays

  import opened Optional

  import opened AltBn128

  import U32

  import U256

  import External

  import ByteUtils

  type EcdsaRecoverFn = (Array<u8>, u8, u256, u256) -> Array<u8>

  type Sha256Fn = Array<u8> -> Array<u8>

  type RipEmd160Fn = Array<u8> -> Array<u8>

  type ModExpFn = (Array<u8>, Array<u8>, Array<u8>) -> Array<u8>

  type Blake2Fn = Array<u8> -> Array<u8>

  type Sha3Fn = Array<u8> -> u256

  datatype T = Dispatcher(ecdsa: EcdsaRecoverFn, sha256: Sha256Fn, ripemd160: RipEmd160Fn, blake2f: Blake2Fn, sha3: Sha3Fn) {
    function {:opaque} Call(address: u160, data: Array<u8>): Option<(Array<u8>, nat)>
      decreases this, address, data
    {
      match address
      case 1 =>
        CallEcdsaRecover(ecdsa, data)
      case 2 =>
        CallSha256(sha256, data)
      case 3 =>
        CallRipEmd160(ripemd160, data)
      case 4 =>
        CallID(data)
      case 5 =>
        CallModExp(data)
      case 6 =>
        CallBnAdd(data)
      case 7 =>
        CallBnMul(data)
      case 8 =>
        CallSnarkV(data)
      case 9 =>
        CallBlake2f(blake2f, data)
      case _ /* _v0 */ =>
        None
    }

    function {:opaque} Sha3(data: Array<u8>): u256
      decreases this, data
    {
      sha3(data)
    }
  }
}

module AltBn128 refines AffineCurve {
  const N: pos := ALT_BN128_PRIME
  const ALT_BN128_PRIME := 21888242871839275222246405745257275088696311157297823662689037894645226208583
  const ALT_BN128_ORDER := 21888242871839275222246405745257275088548364400416034343698204186575808495617
  const A: Element := Value(0)
  const B: Element := Value(3)

  lemma {:axiom} IsPrimeField()
    ensures IsPrime(ALT_BN128_PRIME)
  {
    assume {:axiom} IsPrime(ALT_BN128_PRIME);
  }

  predicate OnCurve(x: Element, y: Element)
    decreases x, y
  {
    y.Pow(2) == x.Pow(3).Add(A.Mul(x)).Add(B)
  }

  lemma LemmaMul1(p: Point)
    requires N > 3 && IsPrime(N)
    ensures p == p.Mul(1)
    decreases p
  {
  }

  lemma LemmaAddMul2(p: Point)
    requires N > 3 && IsPrime(N)
    ensures p.Add(p) == p.Mul(2)
    decreases p
  {
  }

  type Point = p: RawPoint
    | p.Valid()
    witness Infinity

  datatype RawPoint = Pair(Element, Element) | Infinity {
    predicate Valid()
      decreases this
    {
      this.Infinity? || var Pair(x: Element, y: Element) := this; OnCurve(x, y)
    }

    function Add(q: Point): (r: Point)
      requires N > 3 && IsPrime(N)
      requires this.Valid()
      decreases this, q
    {
      if this.Infinity? then
        q
      else if q.Infinity? then
        this
      else if this == q then
        this.Double()
      else
        var Pair(x_p: Element, y_p: Element) := this; var Pair(x_q: Element, y_q: Element) := q; var x_diff: Element := x_q.Sub(x_p); if x_diff == Value(0) then Infinity else var y_diff: Element := y_q.Sub(y_p); var lam: Element := y_diff.Div(x_diff); var x_r: Element := lam.Pow(2).Sub(x_p).Sub(x_q); var y_r: Element := lam.Mul(x_p.Sub(x_r)).Sub(y_p); assume {:axiom} OnCurve(x_r, y_r); Pair(x_r, y_r)
    }

    function Double(): (r: Point)
      requires N > 3 && IsPrime(N)
      requires this.Valid() && this.Pair?
      decreases this
    {
      var Pair(x: Element, y: Element) := this;
      var top: Element := x.Pow(2).Mul(Value(3)).Add(A);
      var bottom: Element := y.Mul(Value(2));
      if bottom == Value(0) then
        Infinity
      else
        var lam: Element := top.Div(bottom); var x_r: Element := lam.Pow(2).Sub(x).Sub(x); var y_r: Element := lam.Mul(x.Sub(x_r)).Sub(y); assume {:axiom} OnCurve(x_r, y_r); Pair(x_r, y_r)
    }

    function Mul(n: nat): (r: Point)
      requires N > 3 && IsPrime(N)
      requires this.Valid()
      decreases n
    {
      if n == 0 then
        Infinity
      else
        var res: Point := this.Add(this).Mul(n / 2); if n % 2 == 1 then this.Add(res) else res
    }
  }

  import opened MathUtils

  type pos = n: nat
    | n > 0
    witness 1

  type Field = n: nat
    | n < N

  datatype Element = Value(n: Field) {
    function Add(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n + rhs.n) % N)
    }

    function Sub(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n - rhs.n) % N)
    }

    function Mul(rhs: Element): Element
      decreases this, rhs
    {
      Value(this.n * rhs.n % N)
    }

    function Div(rhs: Element): Element
      requires IsPrime(N)
      decreases this, rhs
    {
      if rhs.n == 0 then
        Value(0)
      else
        this.Mul(rhs.Inverse())
    }

    function Inverse(): Element
      requires IsPrime(N)
      requires this.n != 0
      decreases this
    {
      var n: Field := this.n;
      assert n < N;
      PrimeFieldsHaveInverse(n, N);
      var inverse: nat := MathUtils.Inverse(n, N).Unwrap();
      Value(inverse)
    }

    function Pow(n: nat): Element
      decreases this, n
    {
      Value(ModPow(this.n, n, N))
    }
  }
}

module AffineCurve refines GaloisField {
  const A: Element
  const B: Element

  predicate OnCurve(x: Element, y: Element)
    decreases x, y
  {
    y.Pow(2) == x.Pow(3).Add(A.Mul(x)).Add(B)
  }

  lemma LemmaMul1(p: Point)
    requires N > 3 && IsPrime(N)
    ensures p == p.Mul(1)
    decreases p
  {
  }

  lemma LemmaAddMul2(p: Point)
    requires N > 3 && IsPrime(N)
    ensures p.Add(p) == p.Mul(2)
    decreases p
  {
  }

  const N: pos

  type Point = p: RawPoint
    | p.Valid()
    witness Infinity

  datatype RawPoint = Pair(Element, Element) | Infinity {
    predicate Valid()
      decreases this
    {
      this.Infinity? || var Pair(x: Element, y: Element) := this; OnCurve(x, y)
    }

    function Add(q: Point): (r: Point)
      requires N > 3 && IsPrime(N)
      requires this.Valid()
      decreases this, q
    {
      if this.Infinity? then
        q
      else if q.Infinity? then
        this
      else if this == q then
        this.Double()
      else
        var Pair(x_p: Element, y_p: Element) := this; var Pair(x_q: Element, y_q: Element) := q; var x_diff: Element := x_q.Sub(x_p); if x_diff == Value(0) then Infinity else var y_diff: Element := y_q.Sub(y_p); var lam: Element := y_diff.Div(x_diff); var x_r: Element := lam.Pow(2).Sub(x_p).Sub(x_q); var y_r: Element := lam.Mul(x_p.Sub(x_r)).Sub(y_p); assume {:axiom} OnCurve(x_r, y_r); Pair(x_r, y_r)
    }

    function Double(): (r: Point)
      requires N > 3 && IsPrime(N)
      requires this.Valid() && this.Pair?
      decreases this
    {
      var Pair(x: Element, y: Element) := this;
      var top: Element := x.Pow(2).Mul(Value(3)).Add(A);
      var bottom: Element := y.Mul(Value(2));
      if bottom == Value(0) then
        Infinity
      else
        var lam: Element := top.Div(bottom); var x_r: Element := lam.Pow(2).Sub(x).Sub(x); var y_r: Element := lam.Mul(x.Sub(x_r)).Sub(y); assume {:axiom} OnCurve(x_r, y_r); Pair(x_r, y_r)
    }

    function Mul(n: nat): (r: Point)
      requires N > 3 && IsPrime(N)
      requires this.Valid()
      decreases n
    {
      if n == 0 then
        Infinity
      else
        var res: Point := this.Add(this).Mul(n / 2); if n % 2 == 1 then this.Add(res) else res
    }
  }

  import opened MathUtils

  type pos = n: nat
    | n > 0
    witness 1

  type Field = n: nat
    | n < N

  datatype Element = Value(n: Field) {
    function Add(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n + rhs.n) % N)
    }

    function Sub(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n - rhs.n) % N)
    }

    function Mul(rhs: Element): Element
      decreases this, rhs
    {
      Value(this.n * rhs.n % N)
    }

    function Div(rhs: Element): Element
      requires IsPrime(N)
      decreases this, rhs
    {
      if rhs.n == 0 then
        Value(0)
      else
        this.Mul(rhs.Inverse())
    }

    function Inverse(): Element
      requires IsPrime(N)
      requires this.n != 0
      decreases this
    {
      var n: Field := this.n;
      assert n < N;
      PrimeFieldsHaveInverse(n, N);
      var inverse: nat := MathUtils.Inverse(n, N).Unwrap();
      Value(inverse)
    }

    function Pow(n: nat): Element
      decreases this, n
    {
      Value(ModPow(this.n, n, N))
    }
  }
}

module GaloisField {
  const N: pos

  import opened MathUtils

  type pos = n: nat
    | n > 0
    witness 1

  type Field = n: nat
    | n < N

  datatype Element = Value(n: Field) {
    function Add(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n + rhs.n) % N)
    }

    function Sub(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n - rhs.n) % N)
    }

    function Mul(rhs: Element): Element
      decreases this, rhs
    {
      Value(this.n * rhs.n % N)
    }

    function Div(rhs: Element): Element
      requires IsPrime(N)
      decreases this, rhs
    {
      if rhs.n == 0 then
        Value(0)
      else
        this.Mul(rhs.Inverse())
    }

    function Inverse(): Element
      requires IsPrime(N)
      requires this.n != 0
      decreases this
    {
      var n: Field := this.n;
      assert n < N;
      PrimeFieldsHaveInverse(n, N);
      var inverse: nat := MathUtils.Inverse(n, N).Unwrap();
      Value(inverse)
    }

    function Pow(n: nat): Element
      decreases this, n
    {
      Value(ModPow(this.n, n, N))
    }
  }
}

module GF2 refines GaloisField {
  const N: pos := 2

  import opened MathUtils

  type pos = n: nat
    | n > 0
    witness 1

  type Field = n: nat
    | n < N

  datatype Element = Value(n: Field) {
    function Add(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n + rhs.n) % N)
    }

    function Sub(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n - rhs.n) % N)
    }

    function Mul(rhs: Element): Element
      decreases this, rhs
    {
      Value(this.n * rhs.n % N)
    }

    function Div(rhs: Element): Element
      requires IsPrime(N)
      decreases this, rhs
    {
      if rhs.n == 0 then
        Value(0)
      else
        this.Mul(rhs.Inverse())
    }

    function Inverse(): Element
      requires IsPrime(N)
      requires this.n != 0
      decreases this
    {
      var n: Field := this.n;
      assert n < N;
      PrimeFieldsHaveInverse(n, N);
      var inverse: nat := MathUtils.Inverse(n, N).Unwrap();
      Value(inverse)
    }

    function Pow(n: nat): Element
      decreases this, n
    {
      Value(ModPow(this.n, n, N))
    }
  }
}

module GF3 refines GaloisField {
  const N: pos := 3

  import opened MathUtils

  type pos = n: nat
    | n > 0
    witness 1

  type Field = n: nat
    | n < N

  datatype Element = Value(n: Field) {
    function Add(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n + rhs.n) % N)
    }

    function Sub(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n - rhs.n) % N)
    }

    function Mul(rhs: Element): Element
      decreases this, rhs
    {
      Value(this.n * rhs.n % N)
    }

    function Div(rhs: Element): Element
      requires IsPrime(N)
      decreases this, rhs
    {
      if rhs.n == 0 then
        Value(0)
      else
        this.Mul(rhs.Inverse())
    }

    function Inverse(): Element
      requires IsPrime(N)
      requires this.n != 0
      decreases this
    {
      var n: Field := this.n;
      assert n < N;
      PrimeFieldsHaveInverse(n, N);
      var inverse: nat := MathUtils.Inverse(n, N).Unwrap();
      Value(inverse)
    }

    function Pow(n: nat): Element
      decreases this, n
    {
      Value(ModPow(this.n, n, N))
    }
  }
}

module GF4 refines GaloisField {
  const N: pos := 4

  import opened MathUtils

  type pos = n: nat
    | n > 0
    witness 1

  type Field = n: nat
    | n < N

  datatype Element = Value(n: Field) {
    function Add(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n + rhs.n) % N)
    }

    function Sub(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n - rhs.n) % N)
    }

    function Mul(rhs: Element): Element
      decreases this, rhs
    {
      Value(this.n * rhs.n % N)
    }

    function Div(rhs: Element): Element
      requires IsPrime(N)
      decreases this, rhs
    {
      if rhs.n == 0 then
        Value(0)
      else
        this.Mul(rhs.Inverse())
    }

    function Inverse(): Element
      requires IsPrime(N)
      requires this.n != 0
      decreases this
    {
      var n: Field := this.n;
      assert n < N;
      PrimeFieldsHaveInverse(n, N);
      var inverse: nat := MathUtils.Inverse(n, N).Unwrap();
      Value(inverse)
    }

    function Pow(n: nat): Element
      decreases this, n
    {
      Value(ModPow(this.n, n, N))
    }
  }
}

module GF5 refines GaloisField {
  const N: pos := 5

  import opened MathUtils

  type pos = n: nat
    | n > 0
    witness 1

  type Field = n: nat
    | n < N

  datatype Element = Value(n: Field) {
    function Add(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n + rhs.n) % N)
    }

    function Sub(rhs: Element): Element
      decreases this, rhs
    {
      Value((this.n - rhs.n) % N)
    }

    function Mul(rhs: Element): Element
      decreases this, rhs
    {
      Value(this.n * rhs.n % N)
    }

    function Div(rhs: Element): Element
      requires IsPrime(N)
      decreases this, rhs
    {
      if rhs.n == 0 then
        Value(0)
      else
        this.Mul(rhs.Inverse())
    }

    function Inverse(): Element
      requires IsPrime(N)
      requires this.n != 0
      decreases this
    {
      var n: Field := this.n;
      assert n < N;
      PrimeFieldsHaveInverse(n, N);
      var inverse: nat := MathUtils.Inverse(n, N).Unwrap();
      Value(inverse)
    }

    function Pow(n: nat): Element
      decreases this, n
    {
      Value(ModPow(this.n, n, N))
    }
  }
}
