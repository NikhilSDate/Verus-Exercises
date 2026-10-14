use std::ptr;

struct Node<V> {
    prev: *mut Node<V>,
    next: *mut Node<V>,
    payload: V,
}

pub struct DList<V> {
    head: *mut Node<V>,
    tail: *mut Node<V>,
}

impl<V> DList<V> {
    pub fn new() -> Self {
        DList {
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
        }
    }

    pub fn push_back(&mut self, v: V) {
        let node = Box::into_raw(Box::new(Node {
            prev: self.tail,
            next: ptr::null_mut(),
            payload: v,
        }));
        if self.tail.is_null() {
            self.head = node;
        } else {
            // SAFETY: tail is non-null, and points to allocated memory.
            unsafe { (*self.tail).next = node };
        }
        self.tail = node;
    }

    pub fn pop_back(&mut self) -> Option<V> {
        if self.tail.is_null() {
            return None;
        }
        // SAFETY: self.tail is non-null, and points to allocated memory. Also, we only free it once.
        let node = unsafe { Box::from_raw(self.tail) };
        self.tail = node.prev;
        if self.tail.is_null() {
            self.head = ptr::null_mut();
        } else {
            // SAFETY: self.tail is non-null, and points to allocated memory
            unsafe { (*self.tail).next = ptr::null_mut() };
        }
        Some(node.payload)
    }
}

fn main() {
    let mut l = DList::new();
    l.push_back(1u32);
    l.push_back(2);
    assert_eq!(l.pop_back(), Some(2));
    assert_eq!(l.pop_back(), Some(1));
    assert_eq!(l.pop_back(), None);
}
