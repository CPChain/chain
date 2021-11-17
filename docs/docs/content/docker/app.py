import os
 
from flask import Flask
from flask import send_from_directory
 
static_file_dir = os.path.join(os.path.dirname(os.path.realpath(__file__)), '../_build')
app = Flask(__name__)
 
 
@app.route('/', methods=['GET'])
def serve_dir_directory_index():
    return send_from_directory(static_file_dir, 'index.html')
 
 
@app.route('/<path:path>', methods=['GET'])
def serve_file_in_dir(path):
    if not os.path.isfile(os.path.join(static_file_dir, path)):
        path = os.path.join(path, 'index.html')
 
    return send_from_directory(static_file_dir, path)
 
if __name__ == '__main__':
    app.run(host='0.0.0.0',port=9528)
