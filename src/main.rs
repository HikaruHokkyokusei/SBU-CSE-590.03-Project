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

    enum Transition {
        CheckIn { book: Book, patron_name: String },
        CheckOut { book: Book, patron_name: String },
    }

    spec fn is_valid_transition(library: Library, transition: Transition, library_prime: Library) -> bool {
        match transition {
            Transition::CheckIn { book, patron_name } => check_in(library, book, patron_name, library_prime),
            Transition::CheckOut { book, patron_name } => check_out(library, book, patron_name, library_prime)
        }
    }

    spec fn next(library: Library, library_prime: Library) -> bool {
        exists |transition: Transition| is_valid_transition(library, transition, library_prime)
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

            assert forall |patron_name: String| has_at_most_one_book(library_prime, patron_name) by {
                // if (exists |transition: Transition| is_valid_transition(library, transition, library_prime)) {
                //     let transition = choose |transition: Transition| is_valid_transition(library, transition, library_prime);
                //     match transition {
                //         Transition::CheckOut { book, patron_name } => {
                //             assert(has_at_most_one_book(library, patron_name));
                //         },
                //         Transition::CheckIn { book, patron_name } => {
                //             assert(has_at_most_one_book(library, patron_name));
                //         }
                //     };
                // } else {
                //     assert(has_at_most_one_book(library, patron_name));
                // }

                assert(has_at_most_one_book(library, patron_name));
            };
        }
    }

    fn main() { }
}
