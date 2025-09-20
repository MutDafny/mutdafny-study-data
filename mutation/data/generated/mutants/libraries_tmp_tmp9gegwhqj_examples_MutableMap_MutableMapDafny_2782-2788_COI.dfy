// libraries_tmp_tmp9gegwhqj_examples_MutableMap_MutableMapDafny.dfy


module {:options "-functionSyntax:4"} MutableMapDafny {
  trait {:termination false} MutableMapTrait<K(==), V(==)> {
    function content(): map<K, V>
      reads this
      decreases {this}

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
      decreases {this}

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
      decreases {this}

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
      decreases {this}

    function Items(): (items: set<(K, V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k: K {:trigger this.content()[k]} {:trigger k in this.content().Keys} | k in this.content().Keys :: (k, this.content()[k])
      decreases {this}

    function Select(k: K): (v: V)
      requires this.HasKey(k)
      reads this
      ensures v in this.content().Values
      ensures this.content()[k] == v
      decreases {this}

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
      decreases {this}
  }

  class MutableMapDafny<K(==), V(==)> extends MutableMapTrait<K, V> {
    var m: map<K, V>

    function content(): map<K, V>
      reads this
      decreases {this}
    {
      m
    }

    constructor ()
      ensures this.content() == map[]
    {
      m := map[];
    }

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}
    {
      m := m[k := v];
      if k in old(m).Keys {
        forall v': V | v' in old(m).Values + {v}
          ensures v' in m.Values + {old(m)[k]}
        {
          if !(v' == v) || v' == old(m)[k] {
            assert m[k] == v;
          } else {
            assert m.Keys == old(m).Keys + {k};
          }
        }
      }
      if k !in old(m).Keys {
        forall v': V | v' in old(m).Values + {v}
          ensures v' in m.Values
        {
          if v' == v {
            assert m[k] == v;
            assert m[k] == v';
            assert v' in m.Values;
          } else {
            assert m.Keys == old(m).Keys + {k};
          }
        }
      }
    }

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
      decreases {this}
    {
      m.Keys
    }

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
      decreases {this}
    {
      k in m.Keys
    }

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
      decreases {this}
    {
      m.Values
    }

    function Items(): (items: set<(K, V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k: K {:trigger this.content()[k]} {:trigger k in this.content().Keys} | k in this.content().Keys :: (k, this.content()[k])
      decreases {this}
    {
      var items: set<(K, V)> := set k: K {:trigger m[k]} {:trigger k in m.Keys} | k in m.Keys :: (k, m[k]);
      assert items == m.Items by {
        forall k: K | k in m.Keys
          ensures (k, m[k]) in m.Items
        {
          assert (k, m[k]) in m.Items;
        }
        assert items <= m.Items;
        forall x: (K, V) | x in m.Items
          ensures x in items
        {
          assert (x.0, m[x.0]) in items;
        }
        assert m.Items <= items;
      }
      items
    }

    function Select(k: K): (v: V)
      requires this.HasKey(k)
      reads this
      ensures v in this.content().Values
      ensures this.content()[k] == v
      decreases {this}
    {
      m[k]
    }

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
    {
      m := map k': K {:trigger m[k']} {:trigger k' in m.Keys} | k' in m.Keys && k' != k :: m[k'];
      if k in old(m).Keys {
        ghost var v := old(m)[k];
        forall v': V | v' in old(m).Values
          ensures v' in m.Values + {v}
        {
          if v' == v {
          } else {
            assert exists k': K {:trigger old(m)[k']} {:trigger k' in m.Keys} | k' in m.Keys :: old(m)[k'] == v';
          }
        }
      }
    }

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
      decreases {this}
    {
      |m|
    }
  }
}
