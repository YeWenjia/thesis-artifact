
# Merging Gradual Typing:

To run the prototype locally, all you need is Java 1.8. Also, check that you have Java 1.8 in the path.

+ JDK8 (https://www.oracle.com/technetwork/java/javase/downloads/)

The following instructions are Unix valid commands. If you have Windows installed in your machine, you need to perform the corresponding commands.
- Unzip the file.
  ```sh
  unzip gmt-bin.zip
  ```
- Go to the "gmt " folder:
  ```sh
  cd gmt-0.9
  ```
- Add run permissions to the binary file:
  ```sh
  chmod +x bin/gmt
  ```
- And then run:
  ```sh
  ./bin/gmt
  ```
  This should start a server in the port 9000. To open the prototype, go to http://localhost:9000/gmt/
- In case the port 9000 is already taken, run:
  ```sh
  ./bin/gmt -Dhttp.port=<available-port-number>
  ```
