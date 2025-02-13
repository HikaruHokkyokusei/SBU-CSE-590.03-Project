use vstd::prelude::*;

verus! {
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

    spec fn init(library: Library) -> bool {
        forall |book: Book| #![auto] library.dom().contains(book) ==> library.index(book) == Card::Shelf
    }

    spec fn check_out(library: Library, book: Book, patron_name: String, library_prime: Library) -> bool {
        &&& library.dom().contains(book)
        &&& library.index(book) == Card::Shelf
        &&& forall |book: Book| #![auto] library.dom().contains(book) ==> library.index(book) != Card::patron(patron_name)
        &&& library_prime == library.insert(book, Card::patron(patron_name))
    }

    spec fn check_in(library: Library, book: Book, patron_name: String, library_prime: Library) -> bool {
        &&& library.dom().contains(book)
        &&& library.index(book) == Card::patron(patron_name)
        &&& library_prime == library.insert(book, Card::Shelf)
    }

    spec fn next(library: Library, library_prime: Library) -> bool {
        ||| exists |book: Book, patron_name: String| check_in(library, book, patron_name, library_prime)
        ||| exists |book: Book, patron_name: String| check_out(library, book, patron_name, library_prime)
    }

    // We will now write this specification a little differently.
    spec fn has_at_most_one_book(library: Library, patron_name: String) -> bool {
        forall |book1: Book, book2: Book| #![auto]
            library.dom().contains(book1) &&
            library.dom().contains(book2) &&
            library.index(book1) == Card::patron(patron_name) &&
            library.index(book2) == Card::patron(patron_name)
            ==> book1 == book2
    }

    spec fn safety(library: Library) -> bool {
        forall |patron_name: String| #![auto] has_at_most_one_book(library, patron_name)
    }

    // Now, even for a correct specification, verus is not able to prove that our system follows
    // the provided proof. Therefore, we need to add hints/triggers to help verus.
    proof fn ensures_safety()
        ensures
        forall |library: Library| init(library) ==> safety(library),
        forall |library: Library, library_prime: Library| safety(library) && next(library, library_prime) ==> safety(library_prime)
    {}

    fn main() { }
}
