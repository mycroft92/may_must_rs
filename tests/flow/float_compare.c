static int subject(float x) {
    if (x > 0.0f) {
        return 1;
    }
    return 0;
}

int main(void) {
    return subject(1.0f);
}
