
module QuickUnion {


    class QuickUnion {
        var n : nat
        var parent: array<nat>
        var size: array<nat>

        constructor(n: nat) 
            requires n > 0
            ensures this.n == n
            ensures this.parent.Length == this.n
            ensures this.size.Length == this.n
            ensures fresh(this)
            ensures Valid()
        {
            parent := new nat[n];
            size := new nat[n];
            this.n := n;
            new;
            assert parent.Length == n;
            assert size.Length == n;
            forall i | 0 <= i < n {
                parent[i] := i;
            }
            forall i | 0 <= i < n {
                size[i] := 1;
            }
        }

        predicate Valid()
            reads this, parent, size
        {
            this.parent.Length > 0 &&
            this.parent.Length == this.size.Length == this.n &&
            this.parent != this.size &&
            (forall i :: 0 <= i < this.parent.Length ==> 0 <= parent[i] < parent.Length)
            && (forall i :: 0 <= i < this.size.Length ==> this.size[i] > 0)
        }

        method findRoot(x: nat) returns (root: nat)
            requires Valid()
            requires 0 <= x < parent.Length
            ensures 0 <= root < parent.Length
            ensures parent.Length == old(parent.Length)
            ensures old(this.n) == this.n
            ensures Valid()
            modifies parent
            decreases *
        {
            root := x;
            // ghost var all := multiset(parent[..]);
            // ghost var visited: set<nat> := {};
            while root != parent[root]
                invariant Valid()
                invariant 0 <= root < parent.Length
                decreases *
            {
                root := parent[root];
            }
            this.parent[x] := root;
        }

        method connected(x: nat, y: nat) returns (result: bool)
            requires 0 <= x < parent.Length
            requires 0 <= y < parent.Length
            requires Valid()
            decreases *
            modifies parent
            ensures old(this.n) == this.n
            ensures Valid()
            ensures fresh(old(this)) ==> fresh(this)
        {
            var xroot := this.findRoot(x);
            var yroot := this.findRoot(y);
            result := xroot == yroot;
        }

        method union(x: nat, y: nat)
            requires 0 <= x < parent.Length
            requires 0 <= y < parent.Length
            requires Valid()
            decreases *
            modifies parent, size
            ensures old(this.n) == this.n
            ensures Valid()
        {
            var rootX := findRoot(x);
            var rootY := findRoot(y);
            if rootX != rootY {
                if size[rootX] < size[rootY] {
                    size[rootY] := size[rootY] + size[rootX];
                    parent[rootX] := rootY;
                } else {
                    size[rootX] := size[rootX] + size[rootY];
                    parent[rootY] := rootX;
                }
            }
        }
    }


class PriorityQueue<T> {
  var heap: array<(T, int)>
  var size: int
  var capacity: int

  constructor (private_capacity: int, def: T)
    requires private_capacity > 0 
    ensures heap.Length == capacity
    ensures size <= heap.Length
    ensures size < capacity
    ensures size == 0
    ensures fresh(this)
  {
    capacity := private_capacity;
    size := 0;
    var default := (def, 0);
    heap := new (T, int)[private_capacity](_ => default);
  }

  method parent(i: int) returns (p: int)
    requires 0 <= i < size
    requires i < heap.Length
    ensures p < heap.Length
    ensures i > 0 ==> 0 <= p < size
    ensures i == 0 ==> p == -1
  {
    if i > 0 {
      p := (i - 1) / 2;
    } else {
      p := -1;
    }
  }

  method leftChild(i: int) returns (l: int)
    requires 0 <= i < size
    ensures l == 2 * i + 1
  {
    l := 2 * i + 1;
  }

  method rightChild(i: int) returns (r: int)
    requires 0 <= i < size
    ensures r == 2 * i + 2
  {
    r := 2 * i + 2;
  }

  method swap(i: int, j: int)
    requires 0 <= i < size && 0 <= j < size
    requires i < heap.Length && j < heap.Length
    modifies heap
    ensures heap[i] == old(heap[j]) && heap[j] == old(heap[i])
  {
    var temp := heap[i];
    heap[i] := heap[j];
    heap[j] := temp;
  }

  method heapifyUp(i: int)
    requires 0 <= i < size
    requires size <= heap.Length
    modifies heap
    decreases i
  {
    var current_parent := parent(i);

    if current_parent >= 0 && current_parent < size
      && 0 <= current_parent < size 
      && heap[i].1 < heap[current_parent].1
    {
      swap(i, current_parent);
      if (current_parent < i) {
        heapifyUp(current_parent); 
      }
    }
  }

  method heapifyDown(i: int)
    requires 0 <= i < size
    modifies heap
    decreases size - i
  {
    var smallest := i;
    var left_child := leftChild(i);
    var right_child := rightChild(i);
    if left_child < size && left_child < heap.Length && heap[left_child].1 < heap[smallest].1 {
      smallest := leftChild(i);
    }
    if right_child < size && right_child < heap.Length && heap[right_child].1 < heap[smallest].1 {
      smallest := rightChild(i);
    }
    if smallest != i {
      swap(i, smallest);
      heapifyDown(smallest);
    }
  }

  method insert(item: T, priority: int)
    requires heap.Length == capacity
    requires 0 <= size < capacity
    modifies this, heap
  {
    heap[size] := (item, priority);
    size := size + 1;
    heapifyUp(size - 1);
  }

  method extractMin() returns (item: T)
    requires size > 0
    requires heap.Length > 0
    requires size - 1 < heap.Length
    modifies this, heap
    ensures size == old(size) - 1
  {
    item := heap[0].0;
    heap[0] := heap[size - 1];
    size := size - 1;
    if size > 0 {
      heapifyDown(0);
    }
  }

  // Peek the element with the smallest priority without removing it
  method peek() returns (item: T)
    requires size > 0
    requires heap.Length > 0
    ensures item == heap[0].0
  {
    item := heap[0].0;
  }

  // Check if the priority queue is empty
  method isEmpty() returns (empty: bool)
    ensures empty == (size == 0)
  {
    empty := (size == 0);
  }
}
}