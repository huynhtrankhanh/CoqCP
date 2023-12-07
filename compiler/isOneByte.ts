export const isOneByte = (x: string): boolean => {
    const encoder = new TextEncoder()
    return encoder.encode(x).length === 1
}