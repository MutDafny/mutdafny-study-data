// fv2020-tms_tmp_tmpnp85b47l_simple_tm.dfy


module ModelingTM {
  method Step(input: TMSystem, pid: ProcessId) returns (system: TMSystem)
    requires pid in input.txQueues
    requires pid in input.procStates
    requires input.validSystem()
    ensures system.validSystem()
    decreases input, pid
  {
    system := input;
    var state: ProcessState := system.procStates[pid];
    assert system.stateValid(pid, state);
    var txs := system.txQueues[pid];
    if state.currentTx >= |txs| {
      return;
    }
    var tx := txs[state.currentTx];
    if state.currentOp == |tx.ops| {
      if state.currentSubOp == 0 {
        if !forall o: int {:trigger o in system.lockedObjs} {:trigger o in state.writeSet} {:trigger o in state.readSet} :: o in state.readSet ==> o in state.writeSet || o !in system.lockedObjs {
          state := new ProcessState.abortTx(state);
          system := new TMSystem.updateState(system, pid, state);
          assume system.validSystem();
          return;
        }
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 1 {
        if !forall o: int {:trigger system.objTimeStamps[o]} {:trigger state.readSet[o]} {:trigger o in state.readSet} :: o in state.readSet ==> state.readSet[o] == system.objTimeStamps[o] {
          state := new ProcessState.abortTx(state);
          system := new TMSystem.updateState(system, pid, state);
          assume system.validSystem();
          return;
        }
        system := new TMSystem.clearDirty(system, state.writeSet);
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 2 {
        system := new TMSystem.updateTimestamps(system, state.writeSet);
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 3 {
        system := new TMSystem.releaseLocks(system, state.writeSet);
        state := new ProcessState.nextTx(state);
      } else {
        assert false;
      }
    } else if state.currentOp == -1 {
      if state.currentSubOp == 0 {
        assert state.currentTx < |system.txQueues[pid]|;
        system := new TMSystem.clearDirty(system, state.writeSet);
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 1 {
        system := new TMSystem.updateTimestamps(system, state.writeSet);
        state := new ProcessState.nextSubOp(state);
      } else if state.currentSubOp == 2 {
        system := new TMSystem.releaseLocks(system, state.writeSet);
        state := new ProcessState.restartTx(state);
      } else {
        assert false;
      }
    } else if state.currentOp >= 0 && state.currentOp < |tx.ops| {
      var op := tx.ops[state.currentOp];
      var o := op.memObject;
      if o !in system.objTimeStamps {
        system := new TMSystem.initTimestamp(system, o);
      }
      assert o in system.objTimeStamps;
      if op.isWrite {
        if state.currentSubOp == 0 {
          if !(op.memObject in state.writeSet) {
            if o in system.lockedObjs {
              state := new ProcessState.abortTx(state);
            } else {
              system := new TMSystem.acquireLock(system, o);
              state := new ProcessState.addToWriteSet(state, o);
              state := new ProcessState.nextSubOp(state);
            }
          } else {
            state := new ProcessState.nextSubOp(state);
          }
        } else if state.currentSubOp == 1 {
          system := new TMSystem.markDirty(system, o);
          state := new ProcessState.nextOp(state);
        } else {
          assert false;
        }
      } else {
        if state.currentSubOp == 0 {
          if o in state.writeSet || o in state.readSet {
            state := new ProcessState.nextOp(state);
          } else {
            state := new ProcessState.addToReadSet(state, o, system.objTimeStamps[o]);
            state := new ProcessState.nextSubOp(state);
          }
        } else if state.currentSubOp == 1 {
          if o in system.lockedObjs {
            state := new ProcessState.abortTx(state);
          } else {
            state := new ProcessState.nextOp(state);
          }
        } else {
          assert false;
        }
      }
    } else {
      assert false;
    }
    system := new TMSystem.updateState(system, pid, state);
    assume system.validSystem();
  }

  type ProcessId = nat

  type MemoryObject = nat

  type TimeStamp = nat

  class Operation {
    const isWrite: bool
    const memObject: MemoryObject
  }

  class Transaction {
    const ops: seq<Operation>
  }

  class ProcessState {
    const currentTx: nat
    const currentOp: int
    const currentSubOp: nat
    const readSet: map<MemoryObject, TimeStamp>
    const writeSet: set<MemoryObject>

    constructor ()
    {
      currentTx := 0;
      currentOp := 0;
      currentSubOp := 0;
      readSet := map[];
      writeSet := {};
    }

    constructor nextSubOp(that: ProcessState)
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == that.currentOp
      ensures this.currentSubOp == that.currentSubOp + 1
      ensures this.readSet == that.readSet
      ensures this.writeSet == that.writeSet
      decreases that
    {
      currentTx := that.currentTx;
      currentOp := that.currentOp;
      currentSubOp := that.currentSubOp + 1;
      readSet := that.readSet;
      writeSet := that.writeSet;
    }

    constructor nextOp(that: ProcessState)
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == that.currentOp + 1
      ensures this.currentSubOp == 0
      ensures this.readSet == that.readSet
      ensures this.writeSet == that.writeSet
      decreases that
    {
      currentTx := that.currentTx;
      currentOp := that.currentOp + 1;
      currentSubOp := 0;
      readSet := that.readSet;
      writeSet := that.writeSet;
    }

    constructor abortTx(that: ProcessState)
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == -1
      ensures this.currentSubOp == 0
      ensures this.readSet == that.readSet
      ensures this.writeSet == that.writeSet
      decreases that
    {
      currentTx := that.currentTx;
      currentOp := -1;
      currentSubOp := 0;
      readSet := that.readSet;
      writeSet := that.writeSet;
    }

    constructor restartTx(that: ProcessState)
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == 0
      ensures this.currentSubOp == 0
      ensures this.readSet == map[]
      ensures this.writeSet == {}
      decreases that
    {
      currentTx := that.currentTx;
      currentOp := 1;
      currentSubOp := 0;
      readSet := map[];
      writeSet := {};
    }

    constructor nextTx(that: ProcessState)
      ensures this.currentTx == that.currentTx + 1
      ensures this.currentOp == 0
      ensures this.currentSubOp == 0
      ensures this.readSet == map[]
      ensures this.writeSet == {}
      decreases that
    {
      currentTx := that.currentTx + 1;
      currentOp := 0;
      currentSubOp := 0;
      readSet := map[];
      writeSet := {};
    }

    constructor addToReadSet(that: ProcessState, obj: MemoryObject, ts: TimeStamp)
      ensures currentTx == that.currentTx
      ensures currentOp == that.currentOp
      ensures currentSubOp == that.currentSubOp
      ensures readSet.Keys == that.readSet.Keys + {obj} && readSet[obj] == ts && forall o: int {:trigger that.readSet[o]} {:trigger readSet[o]} {:trigger o in readSet} :: o in readSet && o != obj ==> readSet[o] == that.readSet[o]
      ensures writeSet == that.writeSet
      decreases that, obj, ts
    {
      currentTx := that.currentTx;
      currentOp := that.currentOp;
      currentSubOp := that.currentSubOp;
      readSet := that.readSet[obj := ts];
      writeSet := that.writeSet;
    }

    constructor addToWriteSet(that: ProcessState, obj: MemoryObject)
      ensures this.currentTx == that.currentTx
      ensures this.currentOp == that.currentOp
      ensures this.currentSubOp == that.currentSubOp
      ensures this.readSet == that.readSet
      ensures this.writeSet == that.writeSet + {obj}
      decreases that, obj
    {
      currentTx := that.currentTx;
      currentOp := that.currentOp;
      currentSubOp := that.currentSubOp;
      readSet := that.readSet;
      writeSet := that.writeSet + {obj};
    }
  }

  class TMSystem {
    const txQueues: map<ProcessId, seq<Transaction>>
    const procStates: map<ProcessId, ProcessState>
    const dirtyObjs: set<MemoryObject>
    const lockedObjs: set<MemoryObject>
    const objTimeStamps: map<MemoryObject, nat>

    constructor (q: map<ProcessId, seq<Transaction>>)
      decreases q
    {
      txQueues := q;
      procStates := map[];
      dirtyObjs := {};
      lockedObjs := {};
      objTimeStamps := map[];
    }

    constructor initTimestamp(that: TMSystem, obj: MemoryObject)
      ensures txQueues == that.txQueues
      ensures procStates == that.procStates
      ensures dirtyObjs == that.dirtyObjs
      ensures lockedObjs == that.lockedObjs
      ensures objTimeStamps.Keys == that.objTimeStamps.Keys + {obj} && objTimeStamps[obj] == 0 && forall o: int {:trigger that.objTimeStamps[o]} {:trigger objTimeStamps[o]} {:trigger o in objTimeStamps} :: o in objTimeStamps && o != obj ==> objTimeStamps[o] == that.objTimeStamps[o]
      decreases that, obj
    {
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs;
      objTimeStamps := that.objTimeStamps[obj := 0];
    }

    constructor updateState(that: TMSystem, pid: ProcessId, state: ProcessState)
      ensures txQueues == that.txQueues
      ensures procStates.Keys == that.procStates.Keys + {pid} && procStates[pid] == state && forall p: int {:trigger that.procStates[p]} {:trigger procStates[p]} {:trigger p in procStates} :: p in procStates && p != pid ==> procStates[p] == that.procStates[p]
      ensures dirtyObjs == that.dirtyObjs
      ensures lockedObjs == that.lockedObjs
      ensures objTimeStamps == that.objTimeStamps
      decreases that, pid, state
    {
      txQueues := that.txQueues;
      procStates := that.procStates[pid := state];
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs;
      objTimeStamps := that.objTimeStamps;
    }

    constructor markDirty(that: TMSystem, obj: MemoryObject)
      ensures txQueues == that.txQueues
      ensures procStates == that.procStates
      ensures dirtyObjs == that.dirtyObjs + {obj}
      ensures lockedObjs == that.lockedObjs
      ensures objTimeStamps == that.objTimeStamps
      decreases that, obj
    {
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs + {obj};
      lockedObjs := that.lockedObjs;
      objTimeStamps := that.objTimeStamps;
    }

    constructor clearDirty(that: TMSystem, writeSet: set<MemoryObject>)
      ensures txQueues == that.txQueues
      ensures procStates == that.procStates
      ensures dirtyObjs == that.dirtyObjs - writeSet
      ensures lockedObjs == that.lockedObjs
      ensures objTimeStamps == that.objTimeStamps
      decreases that, writeSet
    {
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs - writeSet;
      lockedObjs := that.lockedObjs;
      objTimeStamps := that.objTimeStamps;
    }

    constructor acquireLock(that: TMSystem, o: MemoryObject)
      ensures txQueues == that.txQueues
      ensures procStates == that.procStates
      ensures dirtyObjs == that.dirtyObjs
      ensures lockedObjs == that.lockedObjs + {o}
      ensures objTimeStamps == that.objTimeStamps
      decreases that, o
    {
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs + {o};
      objTimeStamps := that.objTimeStamps;
    }

    constructor releaseLocks(that: TMSystem, objs: set<MemoryObject>)
      ensures txQueues == that.txQueues
      ensures procStates == that.procStates
      ensures dirtyObjs == that.dirtyObjs
      ensures lockedObjs == that.lockedObjs - objs
      ensures objTimeStamps == that.objTimeStamps
      decreases that, objs
    {
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs - objs;
      objTimeStamps := that.objTimeStamps;
    }

    constructor updateTimestamps(that: TMSystem, objs: set<MemoryObject>)
      ensures txQueues == that.txQueues
      ensures procStates == that.procStates
      ensures dirtyObjs == that.dirtyObjs
      ensures lockedObjs == that.lockedObjs
      ensures objTimeStamps.Keys == that.objTimeStamps.Keys && forall o: int {:trigger that.objTimeStamps[o]} {:trigger objTimeStamps[o]} {:trigger o in objs} {:trigger o in that.objTimeStamps} :: o in that.objTimeStamps ==> if o in objs then objTimeStamps[o] != that.objTimeStamps[o] else objTimeStamps[o] == that.objTimeStamps[o]
      decreases that, objs
    {
      txQueues := that.txQueues;
      procStates := that.procStates;
      dirtyObjs := that.dirtyObjs;
      lockedObjs := that.lockedObjs;
      objTimeStamps := map o: nat {:trigger that.objTimeStamps[o]} {:trigger o in objs} {:trigger o in that.objTimeStamps} | o in that.objTimeStamps :: if o in objs then that.objTimeStamps[o] + 1 else that.objTimeStamps[o];
    }

    predicate stateValid(pid: ProcessId, state: ProcessState)
      requires pid in procStates && state == procStates[pid]
      decreases pid, state
    {
      pid in txQueues &&
      state.currentTx <= |txQueues[pid]| &&
      if state.currentTx == |txQueues[pid]| then state.currentOp == 0 && state.currentSubOp == 0 && |state.readSet| == 0 && |state.writeSet| == 0 else if state.currentTx < |txQueues[pid]| then true && exists tx: Transaction {:trigger tx.ops} :: tx == txQueues[pid][state.currentTx] && state.currentOp <= |tx.ops| && state.currentOp >= -1 && (if state.currentOp >= 0 && state.currentOp < |tx.ops| then state.currentSubOp < 2 else if state.currentOp == |tx.ops| then state.currentSubOp < 4 else if state.currentOp == -1 then state.currentSubOp < 3 else false) && state.readSet.Keys <= objTimeStamps.Keys && state.writeSet <= lockedObjs else false
    }

    predicate validSystem()
    {
      procStates.Keys <= txQueues.Keys &&
      dirtyObjs <= objTimeStamps.Keys &&
      lockedObjs <= objTimeStamps.Keys &&
      forall p: nat, s: ProcessState {:trigger stateValid(p, s)} :: 
        p in procStates &&
        s == procStates[p] ==>
          stateValid(p, s)
    }
  }
}
