int main(void) {
    int x = 0;
    int *ptr = &x;
    *ptr = 7;
    return *ptr;
}
