
import subprocess
from datetime import datetime

next_test = 1

while next_test <= 1024:
    with open("bufsize.h", "w") as f:
        f.write("#define BUFSIZE %d" % next_test)
    subprocess.Popen("make wc-plain", shell=True).wait()
    subprocess.Popen("make wc-test", shell=True).wait()
    subprocess.Popen("./wc-plain").wait()
    for i in range(5):
        start_time = datetime.now()
        subprocess.Popen("./wc-plain").wait()
        elapsed = datetime.now() - start_time
        print next_test, "plain", elapsed
    subprocess.Popen("./wc-test").wait()
    for i in range(5):
        start_time = datetime.now()
        subprocess.Popen("./wc-test").wait()
        elapsed = datetime.now() - start_time
        print next_test, "test", elapsed
    next_test = next_test * 2
        
