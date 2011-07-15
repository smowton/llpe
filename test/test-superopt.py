
import subprocess
from datetime import datetime

subprocess.Popen("./wc-test").wait()
start_time = datetime.now()
for i in range(1000):
    subprocess.Popen("./wc-test").wait()
elapsed = datetime.now() - start_time
print "Plain: ", elapsed

subprocess.Popen("./wc-superopt").wait()
start_time = datetime.now()
for i in range(1000):
    subprocess.Popen("./wc-superopt").wait()
elapsed = datetime.now() - start_time
print "Opt: ", elapsed

        
