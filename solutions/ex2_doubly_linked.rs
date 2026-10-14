use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {

struct Node<V> {
    prev: Option<PPtr<Node<V>>>,
    next: Option<PPtr<Node<V>>>,
    payload: V,
}

pub struct DList<V> {
    head: Option<PPtr<Node<V>>>,
    tail: Option<PPtr<Node<V>>>,

	len: Ghost<nat>,
    perms: Tracked<Map<nat, PointsTo<Node<V>>>>,
}

impl<V> DList<V> {
    spec fn ptr(&self, i: int) -> PPtr<Node<V>> {
        self.perms@[i as nat].pptr()
    }

    spec fn wf_node(&self, i: int) -> bool {
        &&& self.perms@.dom().contains(i as nat)
        &&& self.perms@[i as nat].is_init()
        &&& self.perms@[i as nat].value().prev == if i == 0 { None } else { Some(self.ptr(i - 1)) }
        &&& self.perms@[i as nat].value().next == if i + 1 == self.len@ { None } else { Some(self.ptr(i + 1)) }
    }

    pub closed spec fn wf(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.len@ ==> #[trigger] self.wf_node(i)
        &&& self.head == if self.len@ == 0 { None } else { Some(self.ptr(0)) }
        &&& self.tail == if self.len@ == 0 { None } else { Some(self.ptr(self.len@ - 1)) }
    }

    pub closed spec fn view(&self) -> Seq<V> {
        Seq::new(self.len@, |i: int| self.perms@[i as nat].value().payload)
    }

    pub fn new() -> (s: Self)
        ensures
            s.wf(),
            s@ == Seq::<V>::empty(),
    {
        DList { head: None, tail: None, len: Ghost(0), perms: Tracked(Map::tracked_empty()) }
    }

    pub fn push_back(&mut self, v: V)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.push(v),
    {
        let ghost n = self.len@ as int;
        match self.tail {
            None => {
                let (ptr, Tracked(perm)) = PPtr::new(Node { prev: None, next: None, payload: v });
                proof {
                    self.perms.borrow_mut().tracked_insert(0, perm);
                }
                self.head = Some(ptr);
                self.tail = Some(ptr);
            },
            Some(tail_ptr) => {
                assert(self.wf_node(n - 1));
                let (ptr, Tracked(perm)) = PPtr::new(Node { prev: Some(tail_ptr), next: None, payload: v });
                tail_ptr.borrow_mut(Tracked(self.perms.borrow_mut().tracked_borrow_mut((n - 1) as nat))).next = Some(ptr);
                proof {
                    self.perms.borrow_mut().tracked_insert(n as nat, perm);
                }
                self.tail = Some(ptr);
            },
        }
        self.len = Ghost(self.len@ + 1);
        assert forall|i: int| 0 <= i < self.len@ implies #[trigger] self.wf_node(i) by {
            if i < n - 1 {
                assert(old(self).wf_node(i));
            }
        }
    }

    pub fn pop_back(&mut self) -> (r: Option<V>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            old(self)@.len() == 0 ==> r == None::<V> && final(self)@ == old(self)@,
            old(self)@.len() > 0 ==> r == Some(old(self)@.last()) && final(self)@ == old(self)@.drop_last(),
    {
        let tail_ptr = self.tail?;
        let ghost n = self.len@ as int;

		assert(self.wf_node(n - 1));
        let tracked tail_perm = self.perms.borrow_mut().tracked_remove((n - 1) as nat);
        let tail_node = tail_ptr.into_inner(Tracked(tail_perm));
        match tail_node.prev {
            None => {
                self.head = None;
                self.tail = None;
            },
            Some(prev_ptr) => {
                assert(old(self).wf_node(n - 2));
                prev_ptr.borrow_mut(Tracked(self.perms.borrow_mut().tracked_borrow_mut((n - 2) as nat))).next = None;
                self.tail = Some(prev_ptr);
            },
        }
        self.len = Ghost((n - 1) as nat);
        assert forall|i: int| 0 <= i < self.len@ implies #[trigger] self.wf_node(i) by {
            assert(old(self).wf_node(i));
        }
        Some(tail_node.payload)
    }
}

fn main() {
    let mut l = DList::new();
    l.push_back(1u32);
    l.push_back(2);
    let a = l.pop_back();
    let b = l.pop_back();
    let c = l.pop_back();
    assert(a == Some(2u32) && b == Some(1u32) && c == None::<u32>);
}

} // verus!
