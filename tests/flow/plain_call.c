__attribute__((noinline)) void touch(int x) {
    (void)x;
}

static int subject(int x) {
    touch(x);
    return x + 1;
}

int main(void) {
    return subject(5);
}
