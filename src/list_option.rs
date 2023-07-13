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

#[extern_spec]
impl<T> std::option::Option<T> {
    #[ensures(result === old(snap(self)))]
    #[ensures(self.is_none())]
    pub fn take(&mut self) -> Option<T>;
}

struct Node {
    elem: i32,
    next: Link,
}

type Link = Option<Box<Node>>;

#[pure]
fn link_len(link: &Link) -> usize {
    match link {
        None => 0,
        Some(node) => 1 + link_len(&node.next),
    }
}

#[pure]
#[requires(index < link_len(link))]
fn link_lookup(link: &Link, index: usize) -> i32 {
    match link {
        Some(node) => {
            if index == 0 {
                node.elem
            } else {
                link_lookup(&node.next, index - 1)
            }
        }
        None => unreachable!(),
    }
}

pub struct List {
    head: Link,
}

impl List {
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: None }
    }

    #[pure]
    pub fn len(&self) -> usize {
        link_len(&self.head)
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        link_lookup(&self.head, index)
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
            next: std::mem::replace(&mut self.head, None),
        });

        self.head = Some(new_node);
    }


    #[pure]
    fn is_empty(&self) -> bool {
        self.head.is_none()
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
        match std::mem::replace(&mut self.head, None) {
            None => None,
            Some(node) => {
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

#[cfg(prusti)]
mod prusti_tests {
    use super::*;

    fn _test_list() {
        let mut list = List::new();
        prusti_assert!(list.is_empty() && list.len() == 0);

        list.push(5);
        list.push(10);
        prusti_assert!(!list.is_empty() && list.len() == 2);
        prusti_assert!(list.lookup(0) == 10);
        prusti_assert!(list.lookup(1) == 5);

        let x = list.pop();
        prusti_assert!(x == 10);

        match list.try_pop() {
            Some (y) => assert!(y == 5),
            None => unreachable!(),
        }

        let z = list.try_pop();
        prusti_assert!(list.is_empty() && list.len() == 0);
        prusti_assert!(z.is_none());
    }
}


#[trusted]
fn print(s: &str) {
    println!("{s}");
}