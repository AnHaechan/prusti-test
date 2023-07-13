use prusti_contracts::*;

#[extern_spec(std::mem)]
#[ensures(snap(dest) === src)]
    // `===`: logical(structural) equality, does not require `PartialEq` like `==`
    // `snap`: snapshot of a refenrence, similar to `clone` 
    // but not requiring `Clone` and ignores borrow checker (-> should only be used in spec)
#[ensures(result === old(snap(dest)))]
fn replace<T> (dest: &mut T, src: T) -> T;

#[extern_spec]
impl<T> std::option::Option<T> {
    #[requires(self.is_some())]
    #[ensures(old(self) === Some(result))]
    pub fn unwrap(self) -> T;

    #[pure]
    #[ensures(result == matches!(self, None))]
    pub const fn is_none(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, Some(_)))]
    pub const fn is_some(&self) -> bool;
}

struct Node {
    elem: i32,
    next: Link,
}

enum Link {
    Empty,
    More(Box<Node>),
}

impl Link {
    #[pure]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(node) => 1 + node.next.len(),
        }
    }

    #[pure]
    fn is_empty(&self) -> bool {
        matches!(self, Link::Empty)
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            Link::More(node) => {
                if index == 0 {
                    node.elem
                } else {
                    node.next.lookup(index - 1)
                }
            }
            Link::Empty => unreachable!(),
        }
    }
}

fn test_len(link: &Link) {
    let link_is_empty = link.is_empty();
    let link_len = link.len();
    assert!(link_is_empty == (link_len == 0)); // Prusti can verify this
}

pub struct List {
    head: Link,
}

impl List {
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }

    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }

    // Three specifications
    // 1. Executing push increases the length of the underlying list by one.
    // 2. After push(elem) the first element of the list stores the value elem.
    // 3. After executing push(elem), the elements of the original list remain unchanged, but are moved back by 1 position.
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)]
    #[ensures(forall(|i: usize| (i < old(self.len())) ==> old(self.lookup(i)) == self.lookup(i+1)))]
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem,
            next: std::mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }


    #[pure]
    fn is_empty(&self) -> bool {
        self.head.is_empty()
    }

    predicate! {
        // If the head of a list was correctly removed
            // 1. The new length is the old length - 1
            // 2. Each element is shifted forwards by one
        fn head_removed(&self, prev: &Self) -> bool {
            self.len() == prev.len() - 1
            && forall (|i: usize|
                (1 <= i && i < prev.len())
                    ==> prev.lookup(i) == self.lookup(i-1))
        }
    }

    // If the input list is empty before the call:
        // The result will be None.
        // The list will still be empty afterwards.
    // If the input list is not empty before the call:
        // The result will be Some(value) and value is the element that was the first element of the list.
        // The length will get reduced by one.
        // All elements will be shifted forwards by one.
    #[ensures(old(self.is_empty()) ==>
        result.is_none() &&
        self.is_empty()
    )]
    #[ensures(!old(self.is_empty()) ==>
        result === Some(old(snap(self)).lookup(0))
        && self.head_removed(&old(snap(self)))
    )]
    pub fn try_pop(&mut self) -> Option<i32> {
        match std::mem::replace(&mut self.head, Link::Empty) {
            Link::Empty => None,
            Link::More(node) => {
                self.head = node.next;
                Some(node.elem)
            },
        }
    }

    #[requires(!self.is_empty())]
    #[ensures(result === old(snap(self)).lookup(0))]
    #[ensures(self.head_removed(&old(snap(self))))]
    pub fn pop(&mut self) -> i32 {
        self.try_pop().unwrap()
    }
}

fn main () {
    let test = Node {
        elem: 17,
        next: Link::Empty
    };

    if test.elem > 23 {
        panic!()
    }
}

#[trusted]
fn print(s: &str) {
    println!("{s}");
}