import time

i = 0

start = time.time()

while i < 100000000:
    i += 1
    
end = time.time()

print(f'Elapsed time: {(end - start):.2f}sec')