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

    spec fn has_at_most_one_book(library: Library, patron_name: String) -> bool {
        forall |book1: Book, book2: Book| #![auto]
            library.dom().contains(book1) &&
            library.dom().contains(book2) &&
            library.index(book1) == Card::patron(patron_name) &&
            library.index(book2) == Card::patron(patron_name)
            ==> book1 == book2
    }

    spec fn safety(library: Library) -> bool {
        forall |patron_name: String| has_at_most_one_book(library, patron_name)
    }

    proof fn ensures_safety()
        ensures
        forall |library: Library| init(library) ==> safety(library),
        forall |library: Library, library_prime: Library| safety(library) && next(library, library_prime) ==> safety(library_prime)
    {
        assert forall |library: Library, library_prime: Library| safety(library) && next(library, library_prime) implies safety(library_prime) by {
            assume(safety(library));
            assume(next(library, library_prime));

            assert forall |patron2: String| has_at_most_one_book(library_prime, patron2) by {
                if (exists |book: Book, patron1: String| check_out(library, book, patron1, library_prime)) {
                    let (book, patron1) = choose |book: Book, patron1: String| check_out(library, book, patron1, library_prime);
                    if (patron2 == patron1) {
                        assert(has_at_most_one_book(library_prime, patron2));
                    } else {
                        assert(has_at_most_one_book(library, patron2));
                        assert(has_at_most_one_book(library_prime, patron1));
                    }
                } else {
                    assert(has_at_most_one_book(library, patron2));
                }
            }
        }
    }

    fn main() { }
}
