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

    type Library = Map<Book, Card>;

    // If we talk in terms of a state machine, the Library if our state.

    fn main() { }
}
