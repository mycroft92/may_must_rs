#include<stdio.h>
#include<stdlib.h>
#include"local_assert.h"

#define MAX_LEN 12

int get_len() {
    int arr[5] = {1,123,0,22,3};
    int idx = rand() % 5;
    return arr[idx];
}

int main(int argc, const char *argv[])
{
    int len  = get_len();
    if(len == 0)
        return -1;

    int i, resultCount, server = 0;
    int allocSize;
    char * buf = NULL;

    if(len != 0)
    {
        resultCount = (len < MAX_LEN) ? len : MAX_LEN;
        allocSize = (resultCount - 1);

        may_assert(len < MAX_LEN);

        buf = malloc(allocSize);
        if(buf == NULL)
            return -1;

        for (i = 0; i < len; i++)
        {
            may_assert(i < MAX_LEN);
            buf[i] = rand() & 0xff;
        }
    }
    free(buf);
    return 0;
}
