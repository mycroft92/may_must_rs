#include <stdio.h>

int main() {
    // Declare and initialize an array
    int numbers[5] = {10, 20, 30, 40, 50};
    int sum = 0;
    int length = 5;
    
    // Print array elements
    printf("Array elements:\n");
    for (int i = 0; i < length; i++) {
        printf("numbers[%d] = %d\n", i, numbers[i]);
    }
    
    // Calculate sum
    for (int i = 0; i < length; i++) {
        sum += numbers[i];
    }
    
    // Calculate and print average
    float average = (float)sum / length;
    printf("\nSum: %d\n", sum);
    printf("Average: %.2f\n", average);
    
    // Find maximum
    int max = numbers[0];
    for (int i = 1; i < length; i++) {
        if (numbers[i] > max) {
            max = numbers[i];
        }
    }
    printf("Maximum: %d\n", max);
    
    return 0;
}
