// Exercise virtual dispatch: a heap-allocated C++ object whose vptr field is
// tracked through the PointerEnv so that the virtual call resolves to the
// concrete callee and its summary can be used to discharge the assertion.
extern "C" void may_assert(bool condition);

class Counter {
public:
    virtual int get() const { return value_; }
    int value_;
};

void test_vtable_dispatch(void) {
    Counter *c = new Counter();
    c->value_ = 42;
    int v = c->get();
    may_assert(v == 42);
}
