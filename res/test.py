import time

i = 0

start = time.time()

def main():
    i = 0

    while i < 1000:
        print("Hello".startswith("He"))     # True
        print("Hello".endswith("lo"))       # True
        print("ell" in "Hello")             # True
        print("Hello".find("l"))            # 2
        print("He" + "llo")                 # "Hello"
        i += 1

main()
    
end = time.time()

print(f'Elapsed time: {(end - start):.2f}sec')