import sys
import hashlib
class WikipediaARC4:
    def __init__(self, key = None):
        self.state = range(256) 
        self.x = self.y = 0 
 
        if key is not None:
            self.init(key)

    def init(self, key):
        for i in range(256):
            self.x = (ord(key[i % len(key)]) + self.state[i] + self.x) & 0xFF
            self.state[i], self.state[self.x] = self.state[self.x], self.state[i]
        self.x = 0
 
    def crypt(self, input):
        output = [None]*len(input)
        for i in xrange(len(input)):
            self.x = (self.x + 1) & 0xFF
            self.y = (self.state[self.x] + self.y) & 0xFF
            self.state[self.x], self.state[self.y] = self.state[self.y], self.state[self.x]
            output[i] = chr((ord(input[i]) ^ self.state[(self.state[self.x] + self.state[self.y]) & 0xFF]))
        return ''.join(output)



        
enc = file("secret", "rb").read()

md5 = enc[:0x10]
enc = enc[0x10:]

print md5.encode("hex")
print hashlib.md5(enc).hexdigest()
if hashlib.md5(enc).digest() != md5 :
    print "FAIL"
    sys.exit(0)
    
unk = 1
l = list(enc)
while unk < len(enc) :
  l[unk - 1] = chr(ord(l[unk - 1]) ^  ord(l[unk]))
  unk+=1
  
enc = "".join(l)
file("decrypt", "wb").write(WikipediaARC4("fd4185ff66a94afde5df94e3f63d8937").crypt(enc))