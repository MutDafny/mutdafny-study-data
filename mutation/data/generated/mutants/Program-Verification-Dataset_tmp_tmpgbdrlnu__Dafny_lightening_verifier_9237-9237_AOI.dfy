// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_lightening_verifier.dfy

predicate ghost_state_inv(s: GhostState)
  decreases s
{
  0 <= s.num_entry * 2 < |s.log| &&
  |s.log| > 0 &&
  |s.mem| == s.mem_len &&
  |s.ideal_mem| == s.mem_len &&
  |s.old_mem| == s.mem_len &&
  s.countdown >= 0
}

function init_ghost_state(log: seq<int>, mem: seq<int>, countdown: int): GhostState
  requires |log| > 0
  requires countdown >= 0
  ensures ghost_state_inv(init_ghost_state(log, mem, countdown))
  decreases log, mem, countdown
{
  GS(0, log[..], |mem|, mem[..], mem[..], mem[..], countdown, map[])
}

function mem_write(s: GhostState, off: int, val: int): GhostState
  requires ghost_state_inv(s)
  requires 0 <= off < s.mem_len
  ensures ghost_state_inv(mem_write(s, off, val))
  decreases s, off, val
{
  var new_mem: seq<int> := s.mem[off := val];
  var new_ideal_mem: seq<int> := s.ideal_mem[off := val];
  s.(mem := new_mem, ideal_mem := new_ideal_mem)
}

function log_write(s: GhostState, off: int, val: int): GhostState
  requires ghost_state_inv(s)
  requires 0 <= off < |s.log|
  ensures ghost_state_inv(log_write(s, off, val))
  decreases s, off, val
{
  s.(log := s.log[off := val])
}

predicate valid_op(s: GhostState, op: GhostOp)
  decreases s, op
{
  match op
  case WriteMem(off, val) =>
    0 <= off < |s.mem|
  case WriteLog(off, val) =>
    0 <= off < |s.log|
}

function countdown(s: GhostState): GhostState
  decreases s
{
  if s.countdown > 0 then
    s.(countdown := s.countdown - 1)
  else
    s
}

function normal_step(s: GhostState, op: GhostOp): GhostState
  requires valid_op(s, op)
  requires ghost_state_inv(s)
  ensures ghost_state_inv(normal_step(s, op))
  decreases s, op
{
  match op
  case WriteMem(off, val) =>
    mem_write(s, off, val)
  case WriteLog(off, val) =>
    log_write(s, off, val)
}

function ghost_step(s: GhostState, op: GhostOp): (GhostState, bool)
  requires valid_op(s, op)
  requires ghost_state_inv(s)
  ensures ghost_state_inv(normal_step(s, op))
  decreases s, op
{
  if s.countdown > 0 then
    var s': GhostState := normal_step(s, op);
    (s'.(countdown := s.countdown - 1), true)
  else
    (s, false)
}

function mem_write_step(s: GhostState, off: int, val: int): (GhostState, bool)
  requires 0 <= off < s.mem_len
  requires ghost_state_inv(s)
  decreases s, off, val
{
  ghost_step(s, WriteMem(off, val))
}

function log_write_step(s: GhostState, off: int, val: int): (GhostState, bool)
  requires 0 <= off < |s.log|
  requires ghost_state_inv(s)
  decreases s, off, val
{
  ghost_step(s, WriteLog(off, val))
}

function set_num_entry(s: GhostState, n: int): (GhostState, bool)
  requires 0 <= n * 2 < |s.log|
  decreases s, n
{
  if s.countdown > 0 then
    (s.(num_entry := n, countdown := s.countdown - 1), true)
  else
    (s, false)
}

predicate crashed(s: GhostState)
  decreases s
{
  s.countdown <= 0
}

predicate old_mem_equiv(s: GhostState)
  requires ghost_state_inv(s)
  decreases s
{
  forall o: int {:trigger s.old_mem[o]} {:trigger s.mem[o]} {:trigger o in s.first_log_pos} :: 
    !(o in s.first_log_pos) &&
    0 <= o < |s.mem| ==>
      s.mem[o] == s.old_mem[o]
}

predicate ghost_tx_inv(s: GhostState)
  decreases s
{
  ghost_state_inv(s) &&
  (forall o: int {:trigger o in s.first_log_pos} :: 
    (o in s.first_log_pos ==>
      0 <= o) &&
    (o in s.first_log_pos ==>
      o < s.mem_len)) &&
  (forall o: int {:trigger s.first_log_pos[o]} {:trigger o in s.first_log_pos} :: 
    (o in s.first_log_pos ==>
      0 <= s.first_log_pos[o]) &&
    (o in s.first_log_pos ==>
      s.first_log_pos[o] < s.num_entry)) &&
  (forall o: int {:trigger s.first_log_pos[o]} {:trigger o in s.first_log_pos} :: 
    (o in s.first_log_pos ==>
      0 <= s.first_log_pos[o] * 2 + 1) &&
    (o in s.first_log_pos ==>
      s.first_log_pos[o] * 2 + 1 < |s.log|)) &&
  (forall o: int {:trigger s.first_log_pos[o]} {:trigger o in s.first_log_pos} :: 
    o in s.first_log_pos ==>
      s.log[s.first_log_pos[o] * 2] == o) &&
  (forall o: int {:trigger s.old_mem[o]} {:trigger s.first_log_pos[o]} {:trigger o in s.first_log_pos} :: 
    o in s.first_log_pos ==>
      s.log[s.first_log_pos[o] * 2 + 1] == s.old_mem[o]) &&
  (forall o: int {:trigger s.first_log_pos[o]} {:trigger o in s.first_log_pos} :: 
    o in s.first_log_pos ==>
      forall i: int {:trigger s.log[i * 2]} :: 
        0 <= i < s.first_log_pos[o] ==>
          s.log[i * 2] != o) &&
  forall i: int {:trigger s.log[i * 2]} :: 
    0 <= i < s.num_entry ==>
      s.log[i * 2] in s.first_log_pos
}

function ghost_begin_tx(s: GhostState): GhostState
  requires ghost_state_inv(s)
  requires s.num_entry == 0
  ensures ghost_state_inv(ghost_begin_tx(s))
  ensures ghost_tx_inv(ghost_begin_tx(s))
  ensures old_mem_equiv(ghost_begin_tx(s))
  decreases s
{
  var (s': GhostState, f: bool) := set_num_entry(s, 0);
  var s': GhostState := s'.(first_log_pos := map[], old_mem := s.mem[..]);
  s'
}

function ghost_commit_tx(s: GhostState): (GhostState, bool)
  requires ghost_tx_inv(s)
  requires old_mem_equiv(s)
  ensures ghost_state_inv(ghost_commit_tx(s).0)
  ensures ghost_tx_inv(ghost_commit_tx(s).0)
  ensures !ghost_commit_tx(s).1 ==> old_mem_equiv(ghost_commit_tx(s).0)
  ensures ghost_commit_tx(s).1 ==> ghost_commit_tx(s).0.num_entry == 0
  decreases s
{
  var s': GhostState := s;
  var (s': GhostState, f: bool) := set_num_entry(s', 0);
  var s': GhostState := if f then s'.(first_log_pos := map[]) else s';
  (s', f)
}

function ghost_tx_write(s0: GhostState, off: int, val: int): GhostState
  requires ghost_tx_inv(s0)
  requires old_mem_equiv(s0)
  requires 0 <= off < s0.mem_len
  requires 0 <= s0.num_entry * 2 + 2 < |s0.log|
  ensures ghost_tx_inv(ghost_tx_write(s0, off, val))
  ensures old_mem_equiv(ghost_tx_write(s0, off, val))
  ensures |ghost_tx_write(s0, off, val).mem| == s0.mem_len
  ensures !crashed(ghost_tx_write(s0, off, val)) ==> ghost_tx_write(s0, off, val).mem[off] == val
  decreases s0, off, val
{
  var s: GhostState := s0;
  var log_idx: int := s.num_entry;
  var log_off: int := log_idx * 2;
  var old_val: int := s.mem[off];
  var (s: GhostState, f: bool) := log_write_step(s, log_off, off);
  var (s: GhostState, f: bool) := log_write_step(s, log_off + 1, old_val);
  var (s: GhostState, f: bool) := set_num_entry(s, log_idx + 1);
  var s: GhostState := if f && !(off in s.first_log_pos) then s.(first_log_pos := s.first_log_pos[off := log_idx]) else s;
  var (s: GhostState, f: bool) := mem_write_step(s, off, val);
  s
}

function reverse_recovery(s0: GhostState, idx: int): GhostState
  requires ghost_tx_inv(s0)
  requires old_mem_equiv(s0)
  requires 0 <= idx <= s0.num_entry
  ensures ghost_tx_inv(reverse_recovery(s0, idx))
  ensures old_mem_equiv(reverse_recovery(s0, idx))
  ensures s0.old_mem == reverse_recovery(s0, idx).old_mem
  ensures s0.first_log_pos == reverse_recovery(s0, idx).first_log_pos
  ensures forall o: int {:trigger s0.mem[o]} {:trigger reverse_recovery(s0, idx).mem[o]} {:trigger s0.first_log_pos[o]} {:trigger o in s0.first_log_pos} :: o in s0.first_log_pos && s0.first_log_pos[o] >= idx ==> reverse_recovery(s0, idx).mem[o] == s0.mem[o]
  ensures forall o: int {:trigger s0.old_mem[o]} {:trigger reverse_recovery(s0, idx).mem[o]} {:trigger s0.first_log_pos[o]} {:trigger o in s0.first_log_pos} :: o in s0.first_log_pos && 0 <= s0.first_log_pos[o] < idx ==> reverse_recovery(s0, idx).mem[o] == s0.old_mem[o]
  decreases idx
{
  if idx == 0 then
    assert old_mem_equiv(s0);
    s0
  else
    var s: GhostState := s0; var i: int := idx - 1; var off: int := s.log[i * 2]; var val: int := s.log[i * 2 + 1]; var s: GhostState := s.(mem := s.mem[off := val]); assert off in s.first_log_pos; var s: GhostState := reverse_recovery(s, idx - 1); assert i == idx - 1; assert forall o: int {:trigger s.old_mem[o]} {:trigger s.mem[o]} {:trigger s.first_log_pos[o]} {:trigger o in s.first_log_pos} :: o in s.first_log_pos && 0 <= s.first_log_pos[o] < i ==> s.mem[o] == s.old_mem[o]; assert forall o: int {:trigger s.old_mem[o]} {:trigger s.first_log_pos[o]} {:trigger o in s.first_log_pos} :: (o in s.first_log_pos && s.first_log_pos[o] == i ==> o == off) && (o in s.first_log_pos && s.first_log_pos[o] == i ==> val == s.old_mem[o]); assert forall o: int {:trigger s.mem[o]} {:trigger s.first_log_pos[o]} {:trigger o in s.first_log_pos} :: o in s.first_log_pos && s.first_log_pos[o] == i ==> s.mem[o] == val; assert old_mem_equiv(s); s
}

function ghost_recover(s0: GhostState): GhostState
  requires ghost_tx_inv(s0)
  requires old_mem_equiv(s0)
  ensures ghost_recover(s0).mem == s0.old_mem
  ensures ghost_recover(s0).num_entry == 0
  decreases s0
{
  var s: GhostState := reverse_recovery(s0, s0.num_entry);
  assert old_mem_equiv(s);
  assert forall o: int {:trigger s0.old_mem[o]} {:trigger s.mem[o]} {:trigger o in s.first_log_pos} :: o in s.first_log_pos ==> s.mem[o] == s0.old_mem[o];
  assert forall i: int {:trigger s0.old_mem[i]} {:trigger s.mem[i]} :: 0 <= i < |s.mem| ==> s.mem[i] == s0.old_mem[i];
  s.(num_entry := 0)
}

lemma crash_safe_single_tx(init_log: seq<int>, init_mem: seq<int>, countdown: int, writes: seq<(int, int)>)
  requires |init_log| > 0
  requires countdown >= 0
  requires forall i: int {:trigger writes[i]} :: (0 <= i < |writes| ==> 0 <= writes[i].0) && (0 <= i < |writes| ==> writes[i].0 < |init_mem|)
  requires 0 < |writes| * 2 < |init_log|
  decreases init_log, init_mem, countdown, writes
{
  ghost var s := init_ghost_state(init_log, init_mem, countdown);
  ghost var end_mem := init_mem;
  s := ghost_begin_tx(s);
  assert s.num_entry == 0;
  assert init_mem == s.old_mem;
  ghost var i := 0;
  while i < |writes|
    invariant 0 <= i <= |writes|
    invariant s.mem_len == |init_mem|
    invariant s.mem_len == |end_mem|
    invariant 0 <= s.num_entry <= i
    invariant |init_log| == |s.log|
    invariant i * 2 < |s.log|
    invariant 0 <= s.num_entry * 2 < |s.log|
    invariant ghost_tx_inv(s)
    invariant old_mem_equiv(s)
    invariant init_mem == s.old_mem
    invariant !crashed(s) ==> forall i: int {:trigger end_mem[i]} {:trigger s.mem[i]} :: 0 <= i < |s.mem| ==> s.mem[i] == end_mem[i]
    decreases |writes| - i
  {
    assert 0 <= i < |writes|;
    assert 0 <= writes[i].0 < s.mem_len;
    assert 0 <= s.num_entry * 2 + 2 < |s.log|;
    s := ghost_tx_write(s, writes[i].0, writes[i].1);
    end_mem := end_mem[writes[i].0 := writes[i].1];
    assert !crashed(s) ==> s.mem[writes[i].0] == writes[i].1;
    i := i + 1;
  }
  assert ghost_tx_inv(s);
  assert old_mem_equiv(s);
  var (s', c) := ghost_commit_tx(s);
  assert c ==> !crashed(s);
  if c {
    assert !crashed(s);
    assert s.mem == end_mem;
  } else {
    ghost var recovered := ghost_recover(s');
    assert recovered.mem == init_mem;
  }
}

class CrashableMem<T> {
  var mem_: array<T>

  method read(off: int) returns (r: T)
    requires 0 <= off < mem_.Length
    decreases off
  {
    return mem_[off];
  }

  method write(off: int, val: T)
    requires 0 <= off < mem_.Length
    modifies mem_
    decreases off
  {
    mem_[off] := val;
  }
}

datatype GhostState = GS(num_entry: int, log: seq<int>, mem_len: int, mem: seq<int>, old_mem: seq<int>, ideal_mem: seq<int>, countdown: int, first_log_pos: map<int, int>)

datatype GhostOp = WriteMem(off: int, val: int) | WriteLog(off: int, val: int)

class UndoLog {
  var log_: array<int>
  var mem_: array<int>
  var impl_countdown: int
  ghost var gs: GhostState

  constructor ()
  {
  }

  predicate ghost_state_equiv(gs: GhostState)
    reads this, mem_, log_
    decreases {this, mem_, log_}, gs
  {
    log_.Length > 0 &&
    mem_[..] == gs.mem &&
    log_[1..] == gs.log &&
    log_[0] == gs.num_entry &&
    impl_countdown == gs.countdown
  }

  predicate state_inv()
    reads this, log_
    decreases {this, log_}
  {
    log_.Length > 1 &&
    0 <= log_[0] &&
    log_[0] * 2 < log_.Length &&
    log_.Length < 4294967295 &&
    mem_ != log_ &&
    forall i: int {:trigger i * 2} :: 
      (0 <= i < log_[0] ==>
        0 <= log_[i * 2 + 1]) &&
      (0 <= i < log_[0] ==>
        log_[i * 2 + 1] < mem_.Length) &&
      (0 <= i < log_[0] ==>
        impl_countdown >= 0)
  }

  method init(log_size: int, mem_size: int, countdown: int)
    requires log_size > 1
    requires mem_size > 0
    requires log_size < 4294967295
    modifies this
    ensures fresh(log_)
    ensures fresh(mem_)
    ensures state_inv()
    ensures ghost_state_equiv(gs)
    decreases log_size, mem_size, countdown
  {
    log_ := new int[log_size];
    mem_ := new int[mem_size];
    log_[0] := 0;
    impl_countdown := countdown;
    gs := GS(0, log_[1..], -mem_size, mem_[..], mem_[..], mem_[..], countdown, map[]);
  }

  method impl_countdown_dec()
    requires impl_countdown > 0
    requires mem_ != log_
    modifies this
    ensures mem_ != log_
    ensures impl_countdown == old(impl_countdown) - 1
    ensures impl_countdown >= 0
    ensures gs == old(gs)
    ensures log_[..] == old(log_)[..]
    ensures mem_[..] == old(mem_)[..]
  {
    impl_countdown := impl_countdown - 1;
  }

  method write_mem(off: int, val: int)
    requires 0 <= off < mem_.Length
    requires mem_ != log_
    requires ghost_state_inv(gs)
    requires ghost_state_equiv(gs)
    requires 0 <= off < gs.mem_len
    modifies this, mem_
    ensures mem_ == old(mem_)
    ensures log_ == old(log_)
    ensures gs == old(gs)
    ensures ghost_state_equiv(mem_write_step(gs, off, val).0)
    decreases off, val
  {
    if impl_countdown > 0 {
      mem_[off] := val;
      impl_countdown := impl_countdown - 1;
    }
  }

  method write_log(off: int, val: int)
    requires 0 <= off <= |gs.log|
    requires mem_ != log_
    requires ghost_state_inv(gs)
    requires ghost_state_equiv(gs)
    requires off == 0 ==> 0 <= val * 2 < |gs.log|
    modifies this, log_
    ensures mem_ != log_
    ensures mem_ == old(mem_)
    ensures log_ == old(log_)
    ensures log_.Length == old(log_).Length
    ensures mem_[..] == old(mem_)[..]
    ensures log_[off] == val || log_[off] == old(log_)[off]
    ensures forall i: int {:trigger old(log_)[i]} {:trigger log_[i]} :: 0 <= i < log_.Length && i != off ==> log_[i] == old(log_)[i]
    ensures gs == old(gs)
    ensures off > 0 ==> ghost_state_equiv(log_write_step(gs, off - 1, val).0)
    ensures off == 0 ==> ghost_state_equiv(set_num_entry(gs, val).0)
    decreases off, val
  {
    if impl_countdown > 0 {
      log_[off] := val;
      impl_countdown := impl_countdown - 1;
    }
  }

  method begin_tx()
    requires state_inv()
    requires ghost_state_equiv(gs)
    requires ghost_state_inv(gs)
    requires log_[0] == 0
    modifies log_, this
    ensures mem_ == old(mem_)
    ensures log_ == old(log_)
    ensures state_inv()
    ensures ghost_state_equiv(gs)
    ensures ghost_tx_inv(gs)
  {
    write_log(0, 0);
    gs := ghost_begin_tx(gs);
    assert state_inv();
  }

  method commit_tx()
    requires state_inv()
    requires ghost_state_equiv(gs)
    requires ghost_state_inv(gs)
    requires ghost_tx_inv(gs)
    requires old_mem_equiv(gs)
    modifies log_, this
    ensures mem_ == old(mem_)
    ensures log_ == old(log_)
    ensures ghost_state_equiv(gs)
    ensures state_inv()
  {
    write_log(0, 0);
    gs := ghost_commit_tx(gs).0;
  }

  method tx_write(offset: int, val: int)
    requires state_inv()
    requires mem_ != log_
    requires 0 <= offset < mem_.Length
    requires ghost_state_equiv(gs)
    requires ghost_tx_inv(gs)
    requires old_mem_equiv(gs)
    requires 0 <= log_[0] * 2 + 3 < log_.Length
    modifies this, log_, mem_
    ensures ghost_state_equiv(gs)
    ensures ghost_tx_inv(gs)
    ensures old_mem_equiv(gs)
    decreases offset, val
  {
    var log_idx := log_[0];
    var log_off := log_idx * 2;
    ghost var old_gs := gs;
    write_log(log_off + 1, offset);
    gs := log_write_step(gs, log_off, offset).0;
    assert log_off + 1 > 0;
    assert ghost_state_equiv(gs);
    assert mem_ != log_;
    var old_val := mem_[offset];
    assert old_val == gs.mem[offset];
    write_log(log_off + 2, old_val);
    gs := log_write_step(gs, log_off + 1, old_val).0;
    assert ghost_tx_inv(gs);
    assert log_[0] == gs.num_entry;
    assert log_.Length == |gs.log| + 1;
    assert 0 <= gs.num_entry * 2 < |gs.log|;
    write_log(0, log_idx + 1);
    ghost var (s, f) := set_num_entry(gs, log_idx + 1);
    s := if f && !(offset in s.first_log_pos) then s.(first_log_pos := s.first_log_pos[offset := log_idx]) else s;
    gs := s;
    write_mem(offset, val);
    gs := mem_write_step(gs, offset, val).0;
    assert gs == ghost_tx_write(old_gs, offset, val);
  }

  method recover()
    requires state_inv()
    requires ghost_tx_inv(gs)
    requires old_mem_equiv(gs)
    requires ghost_state_equiv(gs)
    modifies log_, mem_, this
    ensures gs == ghost_recover(old(gs))
    ensures ghost_state_equiv(gs)
  {
    var log_len := log_[0];
    assert log_len == gs.num_entry;
    if log_len > 0 {
      var i := log_len - 1;
      ghost var gs0 := gs;
      while i >= 0
        invariant log_ == old(log_)
        invariant mem_ == old(mem_)
        invariant unchanged(log_)
        invariant -1 <= i < log_len
        invariant |gs.log| == |gs0.log|
        invariant ghost_state_equiv(gs)
        invariant ghost_tx_inv(gs)
        invariant old_mem_equiv(gs)
        invariant reverse_recovery(gs0, log_len) == reverse_recovery(gs, i + 1)
        decreases i
        modifies mem_, this
      {
        assert ghost_state_equiv(gs);
        assert 0 <= i < log_[0];
        var o := i * 2 + 1;
        var off := log_[o];
        var val := log_[o + 1];
        mem_[off] := val;
        assert 0 <= off < mem_.Length;
        assert gs.log[i * 2] == off;
        assert gs.log[i * 2 + 1] == val;
        gs := gs.(mem := gs.mem[off := val]);
        i := i - 1;
      }
      assert ghost_state_equiv(gs);
    } else {
      assert ghost_state_equiv(gs);
    }
    log_[0] := 0;
    gs := ghost_recover(old(gs));
    assert ghost_state_equiv(gs);
  }
}
