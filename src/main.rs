use vstd::prelude::*;

verus! {
    // Consider we have a Library.
    // In our library, we have books, and each book has a card associated with it.
    // The card tells whether the book is placed in Shelf or borrowed by a Patron.

    // Our Library has a criteria that no two books can be borrowed by the same Patron.

    // Below, we define the Library, Book and Card.
    struct Book {
        title: String
    }

    enum Card {
        Shelf,
        Patron { name: String }
    }

    impl Card {
        spec fn patron(name: String) -> Self {
            Self::Patron { name }
        }
    }

    type Library = Map<Book, Card>;

    // If we talk in terms of a state machine, the Library if our state.

    // We will now specify the initial state of our state machine.
    spec fn init(library: Library) -> bool {
        forall |book: Book| #![auto] library.dom().contains(book) ==> library.index(book) == Card::Shelf
    }

    // We will now define two actions on our state machine.

    // 1. Check Out
    spec fn check_out(library: Library, book: Book, patron_name: String, library_prime: Library) -> bool {
        // Enabling Condition 1
        &&& library.dom().contains(book)
        // Enabling Condition 2
        &&& library.index(book) == Card::Shelf
        // Enabling Condition 3
        &&& forall |book: Book| #![auto] library.dom().contains(book) ==> library.index(book) != Card::patron(patron_name)
        // Update
        &&& library_prime == library.insert(book, Card::patron(patron_name))
    }

    // 2. Check In
    spec fn check_in(library: Library, book: Book, patron_name: String, library_prime: Library) -> bool {
        // Enabling Condition 1
        &&& library.dom().contains(book)
        // Enabling Condition 2
        &&& library.index(book) == Card::patron(patron_name)
        // Update
        &&& library_prime == library.insert(book, Card::Shelf)
    }

    // Finally, we will define next, which specifies whether the new state is a valid next state of the old state
    spec fn next(library: Library, library_prime: Library) -> bool {
        ||| exists |book: Book, patron_name: String| check_in(library, book, patron_name, library_prime)
        ||| exists |book: Book, patron_name: String| check_out(library, book, patron_name, library_prime)
    }

    fn main() { }
}
